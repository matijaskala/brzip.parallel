/*
 * brzip compression utility
 * Copyright (C) 2020  Matija Skala <mskala@gmx.com>
 *
 * brzip is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * brzip is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with brzip.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

#include <ctype.h>
#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <libgen.h>
#include <signal.h>
#ifdef USE_LIBMD
#include <sha256.h>
#else
#include <openssl/sha.h>
#endif
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/sysinfo.h>
#include <unistd.h>

#include <brotli/decode.h>
#include <brotli/encode.h>
#include <pthread.h>
#include <xxhash.h>
#include "gsb_crc32.h"

typedef struct {
	uint8_t *data;
	uint32_t size;
	uint64_t id;
} *packet_t;

typedef struct _offset_list *offset_list_t;

struct _offset_list {
	offset_list_t next;
	off_t off;
};

struct _courier {
	uint8_t check_type;
	uint8_t quality;
	const char *filename;
	const time_t *timestamp;

	uint32_t nthreads;
	uint64_t datalen;
	pthread_t *worker_threads;
	pthread_t muxer_thread;
	FILE *out;

	uint64_t receive_id;
	uint64_t distrib_id;
	uint64_t deliver_id;
	packet_t ibuffer;
	packet_t *obuffer;
	uint32_t working;
	uint32_t slots;
	uint32_t free_slots;
	pthread_mutex_t tmutex;
	pthread_cond_t slot_av;
	pthread_mutex_t imutex;
	pthread_cond_t iav_or_eof;
	pthread_mutex_t omutex;
	pthread_cond_t oav_or_exit;
	bool eof;
	bool error;
	char *input_str;
	char *output_str;
};

typedef struct _courier *courier_t;

static int64_t leap_seconds[][2] = {
#include "leap_seconds.h"
};

static char *output_file = NULL;
static void free_global(char **ptr) {
	void *p = *ptr;
	*ptr = NULL;
	free(p);
}

static time_t tai64tounix(int64_t t) {
	t += 2208988800;
	int l = sizeof leap_seconds/128;
	int i = 0, j = l;
	while (i + 1 < j) {
		if (leap_seconds[(i+j)/2][0] + leap_seconds[(i+j)/2][1] > t)
			j = (i+j)/2;
		else
			i = (i+j)/2;
	}
	t -= 2208988800;
	return t - leap_seconds[i][1];
}

static int64_t unixtotai64(time_t t) {
	t += 2208988800;
	int l = sizeof leap_seconds/128;
	int i = 0, j = l;
	while (i + 1 < j) {
		if (leap_seconds[(i+j)/2][0] > t)
			j = (i+j)/2;
		else
			i = (i+j)/2;
	}
	t -= 2208988800;
	return t + leap_seconds[i][1];
}

courier_t brzip_start(uint8_t quality, uint32_t nthreads, const char *input_str, const char *output_str, FILE *out, void *(*worker)(courier_t), void *(*muxer)(courier_t)) {
	courier_t r = malloc(sizeof *r);
	if (!r)
		err(1, "malloc");
	r->working = r->nthreads = nthreads;
	r->free_slots = r->slots = nthreads > 1 ? nthreads * 2 : 1;
	r->receive_id = r->distrib_id = r->deliver_id = 0;
	r->ibuffer = calloc(r->slots, sizeof *r->ibuffer);
	r->obuffer = calloc(r->slots, sizeof *r->obuffer);
	if (!r->ibuffer || !r->obuffer)
		err(1, "calloc");
	r->input_str = strdup(input_str);
	r->output_str = strdup(output_str);
	if (!r->input_str || !r->output_str)
		err(1, "strdup");
	r->eof = false;
	r->error = false;

	errno = pthread_mutex_init(&r->tmutex, 0);
	if (errno)
		err(1, NULL);
	errno = pthread_cond_init(&r->slot_av, 0);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_init(&r->imutex, 0);
	if (errno)
		err(1, NULL);
	errno = pthread_cond_init(&r->iav_or_eof, 0);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_init(&r->omutex, 0);
	if (errno)
		err(1, NULL);
	errno = pthread_cond_init(&r->oav_or_exit, 0);
	if (errno)
		err(1, NULL);

	r->datalen = 0;
	r->check_type = 3;
	r->filename = NULL;
	r->timestamp = NULL;
	r->quality = quality;
	r->out = out;

	r->worker_threads = malloc(nthreads * sizeof(pthread_t));
	for (uint32_t i = 0; i < nthreads; i++) {
		errno = pthread_create(&r->worker_threads[i], 0, (void *(*)(void*))worker, r);
		if (errno)
			err(1, NULL);
	}
	errno = pthread_create(&r->muxer_thread, 0, (void *(*)(void*))muxer, r);
	if (errno)
		err(1, NULL);
	return r;
}

void brzip_add_block(courier_t ptr, uint8_t *data, uint32_t size) {
	errno = pthread_mutex_lock(&ptr->tmutex);
	if (errno)
		err(1, NULL);
	while (!ptr->free_slots)
		pthread_cond_wait(&ptr->slot_av, &ptr->tmutex);
	ptr->free_slots--;
	errno = pthread_mutex_unlock(&ptr->tmutex);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_lock(&ptr->imutex);
	if (errno)
		err(1, NULL);
	packet_t packet = &ptr->ibuffer[ptr->receive_id % ptr->slots];
	packet->data = data;
	packet->size = size;
	packet->id = ptr->receive_id++;
	errno = pthread_cond_signal(&ptr->iav_or_eof);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_unlock(&ptr->imutex);
	if (errno)
		err(1, NULL);
}

bool brzip_finish(courier_t ptr) {
	errno = pthread_mutex_lock(&ptr->imutex);
	if (errno)
		err(1, NULL);
	ptr->eof = true;
	errno = pthread_cond_broadcast(&ptr->iav_or_eof);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_unlock(&ptr->imutex);
	if (errno)
		err(1, NULL);
	for (uint32_t i = 0; i < ptr->nthreads; i++) {
		errno = pthread_join(ptr->worker_threads[i], NULL);
		if (errno)
			err(1, NULL);
	}
	free(ptr->worker_threads);
	errno = pthread_join(ptr->muxer_thread, NULL);
	if (errno)
		err(1, NULL);

	errno = pthread_cond_destroy(&ptr->oav_or_exit);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_destroy(&ptr->omutex);
	if (errno)
		err(1, NULL);
	errno = pthread_cond_destroy(&ptr->iav_or_eof);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_destroy(&ptr->imutex);
	if (errno)
		err(1, NULL);
	errno = pthread_cond_destroy(&ptr->slot_av);
	if (errno)
		err(1, NULL);
	errno = pthread_mutex_destroy(&ptr->tmutex);
	if (errno)
		err(1, NULL);

	for (size_t i = 0; i < ptr->slots; i++)
		if (ptr->obuffer[i])
			free(ptr->obuffer[i]->data);

	bool ok = !ptr->error;
	free(ptr->ibuffer);
	free(ptr->obuffer);
	free(ptr->input_str);
	free(ptr->output_str);
	free(ptr);

	return ok;
}

static void show_progress() {} // stub

static void *comp_worker(courier_t arg) {
	for (;;) {
		errno = pthread_mutex_lock(&arg->imutex);
		if (errno)
			err(1, NULL);
		packet_t packet = NULL;
		while (arg->receive_id == arg->distrib_id && !arg->eof && !arg->error) {
			errno = pthread_cond_wait(&arg->iav_or_eof, &arg->imutex);
			if (errno)
				err(1, NULL);
		}
		if (arg->receive_id != arg->distrib_id)
			packet = &arg->ibuffer[arg->distrib_id++ % arg->slots];
		errno = pthread_mutex_unlock(&arg->imutex);
		if (errno)
			err(1, NULL);
		if (!packet) {
			errno = pthread_mutex_lock(&arg->omutex);
			if (errno)
				err(1, NULL);
			if (!--arg->working) {
				errno = pthread_cond_signal(&arg->oav_or_exit);
				if (errno)
					err(1, NULL);
			}
			errno = pthread_mutex_unlock(&arg->omutex);
			if (errno)
				err(1, NULL);
			return NULL;
		}
		BrotliEncoderState *encoder = BrotliEncoderCreateInstance(NULL, NULL, NULL);
		if (!encoder)
			err(1, "BrotliEncoderCreateInstance");
		BrotliEncoderSetParameter(encoder, BROTLI_PARAM_QUALITY, arg->quality);
		size_t output_buffer_length = BrotliEncoderMaxCompressedSize(packet->size) + 32;
		size_t namelen = arg->filename ? strlen(arg->filename) : 0;
		if (output_buffer_length == 0 || arg->quality < 2)
			output_buffer_length = packet->size * 2 + 32;
		if (arg->filename)
			output_buffer_length += namelen;
		uint8_t *output_buffer = malloc(output_buffer_length);
		size_t available_in = packet->size;
		const uint8_t *next_in = packet->data;
		size_t available_out = output_buffer_length;
		uint8_t *next_out = output_buffer;
		if (packet->id == 0 && (arg->filename || arg->timestamp)) {
			*next_out = 0;
			if (arg->timestamp)
				*next_out |= 1;
			if (arg->filename)
				*next_out |= 2;
			*next_out |= (0x34cb00 >> ((*next_out ^ (*next_out >> 4)) & 0xf)) & 0x80;
			if (arg->timestamp) {
				int64_t i = unixtotai64(*arg->timestamp < 0 ? ~*arg->timestamp << 1 | 1 : *arg->timestamp << 1);
				do {
					available_out--;
					*++next_out = i & 0x7f;
				} while (i >>= 7);
				*next_out |= 0x80;
			}
			if (arg->filename) {
				int64_t i = namelen;
				do {
					available_out--;
					*++next_out = i & 0x7f;
				} while (i >>= 7);
				*next_out |= 0x80;
				memcpy(next_out + 1, arg->filename, namelen);
				available_out -= namelen;
				next_out += namelen;
			}
			available_out--;
			next_out++;
		}
		do {
			if (!BrotliEncoderCompressStream(encoder, BROTLI_OPERATION_FINISH, &available_in, &next_in, &available_out, &next_out, NULL)) {
				errx(1, "coder failed");
			}
			if (available_out < 16) {
				available_out += output_buffer_length;
				size_t offset = next_out - output_buffer;
				output_buffer = realloc(output_buffer, output_buffer_length *= 2);
				next_out = output_buffer + offset;
			}
		} while (!BrotliEncoderIsFinished(encoder));
		BrotliEncoderDestroyInstance(encoder);
		{
			uint32_t i = packet->size;
			do
				*next_out++ = i & 0x7f;
			while (i >>= 7);
			*(next_out-1) |= 0x80;
		}
		switch (arg->check_type) {
				XXH32_hash_t xxh32sum;
				XXH64_hash_t xxh64sum;
				uint32_t crc32csum;
			case 0:
			case 1:
			case 2:
				xxh32sum = XXH32(packet->data, packet->size, 0);
				for (uint8_t i = 0; i < 1 << arg->check_type; i++) {
					*next_out++ = xxh32sum & 0xff;
					xxh32sum >>= 8;
				}
				break;
			case 3:
				xxh64sum = XXH64(packet->data, packet->size, 0);
				for (uint8_t i = 0; i < 1 << arg->check_type; i++) {
					*next_out++ = xxh64sum & 0xff;
					xxh64sum >>= 8;
				}
				break;
			case 4:
			case 5:
			case 6:
				crc32csum = ~calculate_crc32c(~0, packet->data, packet->size);
				for (uint8_t i = 0; i < 1 << (arg->check_type - 4); i++) {
					*next_out++ = crc32csum & 0xff;
					crc32csum >>= 8;
				}
		}
		free(packet->data);
		errno = pthread_mutex_lock(&arg->omutex);
		if (errno)
			err(1, NULL);
		arg->datalen += packet->size;
		packet->data = output_buffer;
		packet->size = next_out - output_buffer;
		if (packet->size > 0)
			show_progress(packet->size);
		if (arg->obuffer[packet->id % arg->slots])
			errx(1, "internal error");
		arg->obuffer[packet->id % arg->slots] = packet;
		if (packet->id == arg->deliver_id) {
			errno = pthread_cond_signal(&arg->oav_or_exit);
			if (errno)
				err(1, NULL);
		}
		errno = pthread_mutex_unlock(&arg->omutex);
		if (errno)
			err(1, NULL);
	}
}

static void *decomp_worker(courier_t arg) {
	packet_t packet;
	for (;;) {
		errno = pthread_mutex_lock(&arg->imutex);
		if (errno)
			err(1, NULL);
		packet = NULL;
		while (arg->receive_id == arg->distrib_id && !arg->eof && !arg->error) {
			errno = pthread_cond_wait(&arg->iav_or_eof, &arg->imutex);
			if (errno)
				err(1, NULL);
		}
		if (arg->receive_id != arg->distrib_id)
			packet = &arg->ibuffer[arg->distrib_id++ % arg->slots];
		errno = pthread_mutex_unlock(&arg->imutex);
		if (errno)
			err(1, NULL);
		if (!packet) {
			errno = pthread_mutex_lock(&arg->omutex);
			if (errno)
				err(1, NULL);
			if (!--arg->working) {
				errno = pthread_cond_signal(&arg->oav_or_exit);
				if (errno)
					err(1, NULL);
			}
			errno = pthread_mutex_unlock(&arg->omutex);
			if (errno)
				err(1, NULL);
			return NULL;
		}
		size_t output_buffer_length = packet->size * 3;
		uint8_t *output_buffer = malloc(output_buffer_length);
		size_t available_in = packet->size;
		const uint8_t *next_in = packet->data;
		size_t available_out = output_buffer_length;
		uint8_t *next_out = output_buffer;
		for (int iteration = 1; available_in; iteration++) {
			if (packet->id != 0 && iteration != 1) {
				warnx("%s: corrupt input", arg->input_str);
				goto fail;
			}
			if (0x34cb00 >> ((*next_in ^ (*next_in >> 4)) & 0xf) & 0x80) {
				warnx("%s: corrupt input", arg->input_str);
				goto fail;
			}
			uint8_t content_mask = *next_in & 0x7f;
			int check_type = content_mask & 7;
			if (content_mask & 020)
				do {
					available_in--;
					next_in++;
					if (!available_in) {
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					}
				} while ((*next_in & 0x80) == 0);
			available_in--;
			next_in++;
			if (!available_in) {
				warnx("%s: incomplete block", arg->input_str);
				goto fail;
			}
			if (check_type == 7) {
				available_in--;
				next_in++;
				if (!available_in) {
					warnx("%s: incomplete block", arg->input_str);
					goto fail;
				}
			}
			if (content_mask & 0100) {
				if (0x34cb00 >> ((*next_in ^ (*next_in >> 4)) & 0xf) & 0x80) {
					warnx("%s: corrupt input", arg->input_str);
					goto fail;
				}
				uint8_t extra_mask = *next_in;
				if (extra_mask & 1)
					do {
						available_in--;
						next_in++;
						if (!available_in) {
							warnx("%s: incomplete block", arg->input_str);
							goto fail;
						}
					} while ((*next_in & 0x80) == 0);
				if (extra_mask & 2) {
					uint64_t v = 0;
					unsigned exp = 0;
					do {
						if (exp >= 4) {
							warnx("%s: too long stored filename (at %uth byte)", arg->input_str, exp);
							goto fail;
						}
						available_in--;
						next_in++;
						if (!available_in) {
							warnx("%s: incomplete block", arg->input_str);
							goto fail;
						}
						v += (uint32_t)(*next_in & 0x7f) << (exp++ * 7);
					} while ((*next_in & 0x80) == 0);
					available_in -= v;
					next_in += v;
					if (available_in + v <= v) {
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					}
				}
				if (extra_mask & 4) {
					uint64_t v = 0;
					unsigned exp = 0;
					do {
						if (exp * 7 >= 64) {
							warnx("%s: too long extra field (at %uth byte)", arg->input_str, exp);
							goto fail;
						}
						available_in--;
						next_in++;
						if (!available_in) {
							warnx("%s: incomplete block", arg->input_str);
							goto fail;
						}
						v += (uint64_t)(*next_in & 0x7f) << (exp++ * 7);
					} while ((*next_in & 0x80) == 0);
					available_in -= v;
					next_in += v;
					if (available_in + v <= v) {
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					}
				}
				if (extra_mask & 0100) {
					available_in--;
					next_in++;
					if (!available_in) {
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					}
					if (0x34cb00 >> ((*next_in ^ (*next_in >> 4)) & 0xf) & 0x80) {
						warnx("%s: corrupt input", arg->input_str);
						goto fail;
					}
					if (*next_in & 7) {
						warnx("%s: unknown compression method", arg->input_str);
						goto fail;
					}
				}
				if (extra_mask & 040) {
					if (available_in <= 2) {
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					}
					available_in -= 2;
					next_in += 2;
				}
				available_in--;
				next_in++;
				if (!available_in) {
					warnx("%s: incomplete block", arg->input_str);
					goto fail;
				}
			}
			bool finished = false;
			BrotliDecoderState *decoder = BrotliDecoderCreateInstance(NULL, NULL, NULL);
			if (!decoder)
				err(1, "BrotliDecoderCreateInstance");
			while (!finished)
				switch (BrotliDecoderDecompressStream(decoder, &available_in, &next_in, &available_out, &next_out, NULL)) {
					case BROTLI_DECODER_RESULT_SUCCESS:
						finished = true;
						break;
					case BROTLI_DECODER_RESULT_ERROR:
						warnx("%s: brotli decoder failed: %s", arg->input_str, BrotliDecoderErrorString(BrotliDecoderGetErrorCode(decoder)));
						goto fail;
					case BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT:
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					case BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT:
						available_out += output_buffer_length;
						size_t offset = next_out - output_buffer;
						output_buffer = realloc(output_buffer, output_buffer_length *= 2);
						next_out = output_buffer + offset;
				}
			BrotliDecoderDestroyInstance(decoder);
			if (content_mask & 010) {
				uint32_t i = next_out - output_buffer;
				do {
					if (!available_in) {
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					}
					if ((*next_in & 0x7f) != (i & 0x7f)) {
						warnx("%s: invalid uncompressed size", arg->input_str);
						goto fail;
					}
					i >>= 7;
					available_in--;
				} while ((*next_in++ & 0x80) == 0);
				if (i != 0) {
					warnx("%s: invalid uncompressed size", arg->input_str);
					goto fail;
				}
			}
			switch (check_type) {
					XXH32_hash_t xxh32sum;
					XXH64_hash_t xxh64sum;
					uint32_t crc32csum;
					SHA256_CTX sha256;
					uint8_t digest[32];
				case 0:
				case 1:
				case 2:
					xxh32sum = XXH32(output_buffer, next_out - output_buffer, 0);
					for (uint8_t i = 0; i < 1 << check_type; i++) {
						if (!available_in) {
							warnx("%s: incomplete block", arg->input_str);
							goto fail;
						}
						if (*next_in++ != (xxh32sum & 0xff)) {
							warnx("%s: invalid checksum", arg->input_str);
							goto fail;
						}
						available_in--;
						xxh32sum >>= 8;
					}
					break;
				case 3:
					xxh64sum = XXH64(output_buffer, next_out - output_buffer, 0);
					for (uint8_t i = 0; i < 1 << check_type; i++) {
						if (!available_in) {
							warnx("%s: incomplete block", arg->input_str);
							goto fail;
						}
						if (*next_in++ != (xxh64sum & 0xff)) {
							warnx("%s: invalid checksum", arg->input_str);
							goto fail;
						}
						available_in--;
						xxh64sum >>= 8;
					}
					break;
				case 4:
				case 5:
				case 6:
					crc32csum = ~calculate_crc32c(~0, output_buffer, next_out - output_buffer);
					for (uint8_t i = 0; i < 1 << (check_type - 4); i++) {
						if (!available_in) {
							warnx("%s: incomplete block", arg->input_str);
							goto fail;
						}
						if (*next_in++ != (crc32csum & 0xff)) {
							warnx("%s: invalid checksum", arg->input_str);
							goto fail;
						}
						available_in--;
						crc32csum >>= 8;
					}
					break;
				case 7:
					SHA256_Init(&sha256);
					SHA256_Update(&sha256, output_buffer, next_out - output_buffer);
					SHA256_Final(digest, &sha256);
					if (available_in < 32) {
						warnx("%s: incomplete block", arg->input_str);
						goto fail;
					}
					if (memcmp(next_in, digest, 32)) {
						warnx("%s: invalid checksum", arg->input_str);
						goto fail;
					}
					available_in -= 32;
					next_in += 32;
			}
		}
		free(packet->data);
		errno = pthread_mutex_lock(&arg->omutex);
		if (errno)
			err(1, NULL);
		arg->datalen += packet->size;
		packet->data = output_buffer;
		packet->size = next_out - output_buffer;
		if (packet->size > 0)
			show_progress(packet->size);
		if (arg->obuffer[packet->id % arg->slots])
			errx(1, "internal error");
		arg->obuffer[packet->id % arg->slots] = packet;
		if (packet->id == arg->deliver_id) {
			errno = pthread_cond_signal(&arg->oav_or_exit);
			if (errno)
				err(1, NULL);
		}
		errno = pthread_mutex_unlock(&arg->omutex);
		if (errno)
			err(1, NULL);
	}

fail:
	arg->error = true;
	free(packet->data);
	errno = pthread_mutex_lock(&arg->omutex);
	if (errno)
		err(1, NULL);
	if (!--arg->working) {
		errno = pthread_cond_signal(&arg->oav_or_exit);
		if (errno)
			err(1, NULL);
	}
	errno = pthread_mutex_unlock(&arg->omutex);
	if (errno)
		err(1, NULL);
	return NULL;
}

static void *comp_muxer(courier_t arg) {
	uint64_t offset = 1;
	uint32_t i = 0, npackets;
	packet_t packets[arg->slots];
	fputs("\xce\xb2\xcf\x81", arg->out);
	for (;;) {
		npackets = 0;
		errno = pthread_mutex_lock(&arg->omutex);
		if (errno)
			err(1, NULL);
		packet_t *obuffer = &arg->obuffer[arg->deliver_id % arg->slots];
		while (!*obuffer && arg->working > 0) {
			errno = pthread_cond_wait(&arg->oav_or_exit, &arg->omutex);
			if (errno)
				err(1, NULL);
		}
		while (*obuffer) {
			packets[npackets++] = *obuffer;
			*obuffer = NULL;
			obuffer = &arg->obuffer[++arg->deliver_id % arg->slots];
		}
		errno = pthread_mutex_unlock(&arg->omutex);
		if (errno)
			err(1, NULL);
		if (!npackets) {
			if (fputc(077, arg->out) < 0)
				goto fail;
			if (fputc((offset & 0x7f) | 0x80, arg->out) < 0)
				goto fail;
			while ((offset >>= 7) > 0x7f)
				if (fputc(offset & 0x7f, arg->out) < 0)
					goto fail;
			if (fputc((offset & 0x7f) | 0x80, arg->out) < 0)
				goto fail;
			if (fputc((arg->datalen & 0x7f) | 0x80, arg->out) < 0)
				goto fail;
			while ((arg->datalen >>= 7) > 0x7f)
				if (fputc(arg->datalen & 0x7f, arg->out) < 0)
					goto fail;
			if (fputc((arg->datalen & 0x7f) | 0x80, arg->out) < 0)
				goto fail;
			if (fputc(077, arg->out) < 0)
				goto fail;
			return NULL;
		}
		for (i = 0; i < npackets; i++) {
			packet_t packet = packets[i];
			uint8_t content_mask = arg->check_type | 010;
			if (offset > 1)
				content_mask |= 020;
			if (packet->id == 0 && (arg->filename || arg->timestamp))
				content_mask |= 0100;
			if (fputc(((0x34cb00 >> ((content_mask ^ (content_mask >> 4)) & 0xf)) & 0x80) | content_mask, arg->out) < 0)
				goto fail;
			if (offset > 1) {
				uint8_t i = 2;
				while (offset > 0x7f) {
					if (fputc(offset & 0x7f, arg->out) < 0)
						goto fail;
					offset >>= 7;
					i++;
				}
				if (fputc((offset & 0x7f) | 0x80, arg->out) < 0)
					goto fail;
				offset = i;
			}
			offset += packet->size;
			if (fwrite(packet->data, 1, packet->size, arg->out) != packet->size)
				goto fail;
			free(packet->data);
			errno = pthread_mutex_lock(&arg->tmutex);
			if (errno)
				err(1, NULL);
			if (++arg->free_slots == 1) {
				errno = pthread_cond_signal(&arg->slot_av);
				if (errno)
					err(1, NULL);
			}
			errno = pthread_mutex_unlock(&arg->tmutex);
			if (errno)
				err(1, NULL);
		}
	}

fail:
	warn("%s", arg->output_str);
	arg->error = true;
	while (i < npackets)
		free(packets[i++]->data);
	return NULL;
}

static void *decomp_muxer(courier_t arg) {
	packet_t packets[arg->slots];
	for (;;) {
		uint32_t npackets = 0;
		errno = pthread_mutex_lock(&arg->omutex);
		if (errno)
			err(1, NULL);
		packet_t *obuffer = &arg->obuffer[arg->deliver_id % arg->slots];
		while (!*obuffer && arg->working > 0) {
			errno = pthread_cond_wait(&arg->oav_or_exit, &arg->omutex);
			if (errno)
				err(1, NULL);
		}
		while (*obuffer) {
			packets[npackets++] = *obuffer;
			*obuffer = NULL;
			obuffer = &arg->obuffer[++arg->deliver_id % arg->slots];
		}
		errno = pthread_mutex_unlock(&arg->omutex);
		if (errno)
			err(1, NULL);
		if (!npackets)
			return NULL;
		for (uint32_t i = 0; i < npackets; i++) {
			packet_t packet = packets[i];
			if (fwrite(packet->data, 1, packet->size, arg->out) != packet->size) {
				warn("%s", arg->output_str);
				arg->error = true;
				while (i < npackets)
					free(packets[i++]->data);
				return NULL;
			}
			free(packet->data);
			errno = pthread_mutex_lock(&arg->tmutex);
			if (errno)
				err(1, NULL);
			if (++arg->free_slots == 1) {
				errno = pthread_cond_signal(&arg->slot_av);
				if (errno)
					err(1, NULL);
			}
			errno = pthread_mutex_unlock(&arg->tmutex);
			if (errno)
				err(1, NULL);
		}
	}
}

static bool brzip_decompress1(const char *input_str, const char *output_str, FILE *in, FILE *out) {
	XXH32_state_t *xxh32 = XXH32_createState();
	XXH64_state_t *xxh64 = XXH64_createState();
	XXH32_state_t *xxh32full = XXH32_createState();
	XXH64_state_t *xxh64full = XXH64_createState();
	if (!xxh32 || !xxh32full)
		err(1, "XXH32_createState");
	if (!xxh64 || !xxh64full)
		err(1, "XXH64_createState");
	XXH32_reset(xxh32full, 0);
	XXH64_reset(xxh64full, 0);
	uint32_t crc32cfull = ~calculate_crc32c(~0, NULL, 0);
	size_t total_size = 0;
	size_t input_buffer_length = 1 << 18;
	size_t output_buffer_length = 1 << 18;
	void *input_buffer = malloc(input_buffer_length);
	uint8_t *output_buffer = malloc(output_buffer_length);
	if (!input_buffer || !output_buffer)
		err(1, "malloc");
	uint64_t offset = 0;
	const uint8_t *next_in = input_buffer;
	size_t available_in = fread(input_buffer, 1, input_buffer_length, in);
	if (!available_in) {
		warnx("%s: unexpected end of file", input_str);
		goto fail;
	}
	for (;;) {
		SHA256_CTX sha256;
		uint32_t crc32csum = ~calculate_crc32c(~0, NULL, 0);
		uint64_t block_size = 0;
		uint64_t old_offset = offset;
		offset = 0;
		if (0x34cb00 >> ((*next_in ^ (*next_in >> 4)) & 0xf) & 0x80) {
			warnx("%s: corrupt input", input_str);
			goto fail;
		}
		uint8_t content_mask = *next_in & 0x7f;
		if ((content_mask & 0140) == 0140) {
			warnx("%s: corrupt input", input_str);
			goto fail;
		}
		offset++;
		available_in--;
		next_in++;
		if (!available_in && content_mask != 047) {
			next_in = input_buffer;
			available_in = fread(input_buffer, 1, input_buffer_length, in);
			if (!available_in) {
				warnx("%s: unexpected end of file", input_str);
				goto fail;
			}
		}
		int check_type = content_mask & 7;
		if (content_mask & 020) {
			int64_t i = old_offset;
			if (content_mask & 040) {
				if ((*next_in & 0x80) == 0) {
					warnx("%s: corrupt input", input_str);
					goto fail;
				}
				if ((*next_in & 0x7f) != (i & 0x7f)) {
					warnx("%s: invalid offset", input_str);
					goto fail;
				}
				i >>= 7;
				offset++;
				available_in--;
				next_in++;
			}
			do {
				if (!available_in) {
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
				if ((*next_in & 0x7f) != (i & 0x7f)) {
					warnx("%s: invalid offset", input_str);
					goto fail;
				}
				i >>= 7;
				offset++;
				available_in--;
			} while ((*next_in++ & 0x80) == 0);
			if (i != 0) {
				warnx("%s: invalid offset", input_str);
				goto fail;
			}
			if (!available_in) {
				next_in = input_buffer;
				available_in = fread(input_buffer, 1, input_buffer_length, in);
				if (!available_in) {
					warnx("%s: unexpected end of file", input_str);
					goto fail;
				}
			}
		}
		switch (check_type) {
			case 0:
			case 1:
			case 2:
				XXH32_reset(xxh32, 0);
				break;
			case 3:
				XXH64_reset(xxh64, 0);
				break;
			case 7:
				if (content_mask & 040)
					break;
				if (*next_in != 0) {
					warnx("%s: unsupported checksum type", input_str);
					goto fail;
				}
				offset++;
				available_in--;
				next_in++;
				if (!available_in) {
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
				SHA256_Init(&sha256);
		}
		if (content_mask & 0100) {
			if (0x34cb00 >> ((*next_in ^ (*next_in >> 4)) & 0xf) & 0x80) {
				warnx("%s: corrupt input", input_str);
				goto fail;
			}
			uint8_t extra_mask = *next_in;
			if (extra_mask & 1)
				do {
					offset++;
					available_in--;
					next_in++;
					if (!available_in) {
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					}
				} while ((*next_in & 0x80) == 0);
			if (extra_mask & 2) {
				uint64_t v = 0;
				unsigned exp = 0;
				do {
					if (exp >= 4) {
						warnx("%s: too long stored filename (at %uth byte)", input_str, exp);
						goto fail;
					}
					offset++;
					available_in--;
					next_in++;
					if (!available_in) {
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					}
					v += (uint32_t)(*next_in & 0x7f) << (exp++ * 7);
				} while ((*next_in & 0x80) == 0);
				offset += v;
				available_in -= v;
				next_in += v;
				if (available_in + v <= v) {
					if (available_in + v < v)
						if (fread(input_buffer, 1, -available_in, in) + available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
			}
			if (extra_mask & 4) {
				uint64_t v = 0;
				unsigned exp = 0;
				do {
					if (exp * 7 >= 64) {
						warnx("%s: too long extra field (at %uth byte)", input_str, exp);
						goto fail;
					}
					offset++;
					available_in--;
					next_in++;
					if (!available_in) {
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					}
					v += (uint64_t)(*next_in & 0x7f) << (exp++ * 7);
				} while ((*next_in & 0x80) == 0);
				offset += v;
				available_in -= v;
				next_in += v;
				if (available_in + v <= v) {
					if (available_in + v < v)
						if (fread(input_buffer, 1, -available_in, in) + available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
			}
			if (extra_mask & 0100) {
				offset++;
				available_in--;
				next_in++;
				if (!available_in) {
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
				if (0x34cb00 >> ((*next_in ^ (*next_in >> 4)) & 0xf) & 0x80) {
					warnx("%s: corrupt input", input_str);
					goto fail;
				}
				if (*next_in & 7) {
					warnx("%s: unknown compression method", input_str);
					goto fail;
				}
			}
			if (extra_mask & 040) {
				offset += 2;
				available_in -= 2;
				next_in += 2;
				if (available_in + 2 <= 2) {
					if (available_in + 2 < 2)
						if (fread(input_buffer, 1, -available_in, in) + available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
			}
			offset++;
			available_in--;
			next_in++;
			if (!available_in) {
				next_in = input_buffer;
				available_in = fread(input_buffer, 1, input_buffer_length, in);
				if (!available_in) {
					warnx("%s: unexpected end of file", input_str);
					goto fail;
				}
			}
		}
		if ((content_mask & 040) == 0) {
			bool finished = false;
			size_t len;
			BrotliDecoderState *decoder = BrotliDecoderCreateInstance(NULL, NULL, NULL);
			if (!decoder)
				err(1, "BrotliDecoderCreateInstance");
			size_t available_out = output_buffer_length;
			uint8_t *next_out = output_buffer;
			offset += available_in;
			while (!finished)
				switch (BrotliDecoderDecompressStream(decoder, &available_in, &next_in, &available_out, &next_out, NULL)) {
					case BROTLI_DECODER_RESULT_SUCCESS:
						finished = true;
						break;
					case BROTLI_DECODER_RESULT_ERROR:
						warnx("%s: brotli decoder failed: %s", input_str, BrotliDecoderErrorString(BrotliDecoderGetErrorCode(decoder)));
						goto fail;
					case BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT:
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
						offset += available_in;
						break;
					case BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT:
						len = fwrite(output_buffer, 1, output_buffer_length - available_out, out);
						if (!len) {
							warn("%s", output_str);
							goto fail;
						}
						switch (check_type) {
							case 0:
							case 1:
							case 2:
								XXH32_update(xxh32, output_buffer, len);
								break;
							case 3:
								XXH64_update(xxh64, output_buffer, len);
								break;
							case 4:
							case 5:
							case 6:
								crc32csum = ~calculate_crc32c(~crc32csum, output_buffer, len);
								break;
							case 7:
								SHA256_Update(&sha256, output_buffer, len);
						}
						block_size += len;
						available_out += len;
						next_out -= len;
						memmove(output_buffer, output_buffer + len, output_buffer_length - available_out);
				}
			offset -= available_in;
			len = output_buffer_length - available_out;
			switch (check_type) {
				case 0:
				case 1:
				case 2:
					XXH32_update(xxh32, output_buffer, len);
					break;
				case 3:
					XXH64_update(xxh64, output_buffer, len);
					break;
				case 4:
				case 5:
				case 6:
					crc32csum = ~calculate_crc32c(~crc32csum, output_buffer, len);
					break;
				case 7:
					SHA256_Update(&sha256, output_buffer, len);
			}
			total_size += block_size += len;
			BrotliDecoderDestroyInstance(decoder);
			if (fwrite(output_buffer, 1, len, out) != len) {
				warn("%s", output_str);
				goto fail;
			}
		}
		if (content_mask & 010) {
			uint32_t i = (content_mask & 040) ? total_size : block_size;
			if (content_mask & 040) {
				if (!available_in) {
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
				if ((*next_in & 0x80) == 0) {
					warnx("%s: corrupt input", input_str);
					goto fail;
				}
				if ((*next_in & 0x7f) != (i & 0x7f)) {
					warnx("%s: invalid uncompressed size", input_str);
					goto fail;
				}
				i >>= 7;
				offset++;
				available_in--;
				next_in++;
			}
			do {
				if (!available_in) {
					next_in = input_buffer;
					available_in = fread(input_buffer, 1, input_buffer_length, in);
					if (!available_in) {
						warnx("%s: unexpected end of file", input_str);
						goto fail;
					}
				}
				if ((*next_in & 0x7f) != (i & 0x7f)) {
					warnx("%s: invalid uncompressed size", input_str);
					goto fail;
				}
				i >>= 7;
				offset++;
				available_in--;
			} while ((*next_in++ & 0x80) == 0);
			if (i != 0) {
				warnx("invalid uncompressed size");
				goto fail;
			}
		}
		switch (check_type) {
				XXH32_hash_t xxh32sum;
				XXH64_hash_t xxh64sum;
				uint8_t digest[32];
			case 0:
			case 1:
			case 2:
				xxh32sum = XXH32_digest(xxh32);
				for (uint8_t i = 0; i < 1 << check_type; i++) {
					if (!available_in) {
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					}
					if (*next_in++ != (digest[i] = xxh32sum & 0xff)) {
						warnx("invalid checksum");
						goto fail;
					}
					offset++;
					available_in--;
					xxh32sum >>= 8;
				}
				XXH32_update(xxh32full, digest, 1 << check_type);
				XXH64_update(xxh64full, digest, 1 << check_type);
				crc32cfull = ~calculate_crc32c(~crc32cfull, digest, 1 << check_type);
				break;
			case 3:
				xxh64sum = XXH64_digest(xxh64);
				for (uint8_t i = 0; i < 1 << check_type; i++) {
					if (!available_in) {
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					}
					if (*next_in++ != (digest[i] = xxh64sum & 0xff)) {
						warnx("invalid checksum");
						goto fail;
					}
					offset++;
					available_in--;
					xxh64sum >>= 8;
				}
				XXH32_update(xxh32full, digest, 1 << check_type);
				XXH64_update(xxh64full, digest, 1 << check_type);
				crc32cfull = ~calculate_crc32c(~crc32cfull, digest, 1 << check_type);
				break;
			case 4:
			case 5:
			case 6:
				for (uint8_t i = 0; i < 1 << (check_type - 4); i++) {
					if (!available_in) {
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					}
					if (*next_in++ != (digest[i] = crc32csum & 0xff)) {
						warnx("invalid checksum");
						goto fail;
					}
					offset++;
					available_in--;
					crc32csum >>= 8;
				}
				XXH32_update(xxh32full, digest, 1 << (check_type - 4));
				XXH64_update(xxh64full, digest, 1 << (check_type - 4));
				crc32cfull = ~calculate_crc32c(~crc32cfull, digest, 1 << (check_type - 4));
				break;
			case 7:
				if (content_mask & 040)
					break;
				SHA256_Final(digest, &sha256);
				for (uint8_t i = 0; i < 32; i++) {
					if (!available_in) {
						next_in = input_buffer;
						available_in = fread(input_buffer, 1, input_buffer_length, in);
						if (!available_in) {
							warnx("%s: unexpected end of file", input_str);
							goto fail;
						}
					}
					if (*next_in++ != digest[i]) {
						warnx("invalid checksum");
						goto fail;
					}
					offset++;
					available_in--;
				}
				XXH32_update(xxh32full, digest, 32);
				XXH64_update(xxh64full, digest, 32);
				crc32cfull = ~calculate_crc32c(~crc32cfull, digest, 32);
				break;
			default:
				warnx("%s: corrupt input", input_str);
				goto fail;
		}
		if (content_mask & 040) {
			if (content_mask != 047) {
				if (0x34cb00 >> ((*next_in ^ (*next_in >> 4)) & 0xf) & 0x80 || (*next_in & 0x7f) != content_mask) {
					warnx("%s: corrupt input %d", input_str, *next_in);
					goto fail;
				}
				offset++;
				available_in--;
				next_in++;
			}
			int c;
			while ((available_in-- && (c = *next_in++, true)) || (c = fgetc(in)) != EOF)
				if (c) {
					warnx("%s: unexpected nonzero character '\\x%x' near the end of file", input_str, c);
					goto fail;
				}
			XXH32_freeState(xxh32);
			XXH64_freeState(xxh64);
			XXH32_freeState(xxh32full);
			XXH64_freeState(xxh64full);
			free(output_buffer);
			free(input_buffer);
			return true;
		}
	}
	abort();

fail:
	XXH32_freeState(xxh32);
	XXH64_freeState(xxh64);
	XXH32_freeState(xxh32full);
	XXH64_freeState(xxh64full);
	free(output_buffer);
	free(input_buffer);
	return false;
}

static bool brzip_decompress_stdin() {
	char buf[4];
	if (fread(buf, 1, 4, stdin) != 4) {
		if (feof(stdin))
			warnx("%s: unexpected end of file", "stdin");
		else
			warn("stdin");
		return false;
	}
	if (memcmp(buf, "\xce\xb2\xcf\x81", 4)) {
		warnx("%s: not in br format", "stdin");
		return false;
	}
	return brzip_decompress1("stdin", "stdout", stdin, stdout);
}

static bool brzip_decompress_file(uint32_t nthreads, const char *input_file, bool to_stdout, bool keep, bool force) {
	FILE *in = NULL, *out = NULL;
	struct stat st;
	char *f = NULL;
	struct timespec times[2];
	if (to_stdout) {
		in = fopen(input_file, "rb");
		if (!in) {
			warn("%s", input_file);
			return false;
		}
		char buf[4];
		if (fread(buf, 1, 4, in) != 4) {
			if (feof(in))
				warnx("%s: unexpected end of file", input_file);
			else
				warn("%s", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		if (memcmp(buf, "\xce\xb2\xcf\x81", 4)) {
			warnx("%s: not in br format", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		if (fstat(fileno(in), &st) < 0) {
			warn("%s", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		if (!S_ISREG(st.st_mode)) {
			if (!brzip_decompress1(input_file, "stdout", in, stdout))
				goto fail;
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return true;
		}
		times[0] = st.st_atim;
		times[1] = st.st_mtim;
		out = stdout;
	}
	else {
		if (lstat(input_file, &st) < 0) {
			warn("%s", input_file);
			return false;
		}
		if (!S_ISREG(st.st_mode)) {
			warnx("%s is not a regular file -- ignored", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		times[0] = st.st_atim;
		times[1] = st.st_mtim;
		in = fopen(input_file, "rb");
		if (!in) {
			warn("%s", input_file);
			return false;
		}
		char buf[4];
		if (fread(buf, 1, 4, in) != 4) {
			if (feof(in))
				warnx("%s: unexpected end of file", input_file);
			else
				warn("%s", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		if (memcmp(buf, "\xce\xb2\xcf\x81", 4)) {
			warnx("%s: not in br format", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		int c = fgetc(in);
		if (c == EOF) {
			warnx("%s: unexpected end of file", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		if (c & 020)
			for (;;) {
				int c = fgetc(in);
				if (c == EOF) {
					warnx("%s: unexpected end of file", input_file);
					if (fclose(in) < 0)
						err(1, "%s", input_file);
					return false;
				}
				if ((fgetc(in) & 0x80) != 0)
					break;
			}
		if ((c & 7) == 7 && fgetc(in) == EOF) {
			warnx("%s: unexpected end of file", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		if (c & 0100) {
			c = fgetc(in);
			if (c == EOF) {
				warnx("%s: unexpected end of file", input_file);
				if (fclose(in) < 0)
					err(1, "%s", input_file);
				return false;
			}
			if (c & 1) {
				uint64_t v = 0;
				unsigned exp = 0;
				do {
					if (exp >= 9)
						errx(1, "%s: too long timestamp (at %uth byte)", input_file, exp);
					c = fgetc(in);
					if (c == EOF) {
						warnx("%s: unexpected end of file", input_file);
						if (fclose(in) < 0)
							err(1, "%s", input_file);
						return false;
					}
					v += (off_t)(c & 0x7f) << (exp++ * 7);
				} while ((c & 0x80) == 0);
				times[1] = (struct timespec) { .tv_sec = tai64tounix(v & 1 ? ~(v >> 1) : (v >> 1)), .tv_nsec = 0 };
			}
			if (c & 2) {
				uint64_t v = 0;
				unsigned exp = 0;
				do {
					if (exp >= 4)
						errx(1, "%s: too long stored filename (at %uth byte)", input_file, exp);
					c = fgetc(in);
					if (c == EOF) {
						warnx("%s: unexpected end of file", input_file);
						if (fclose(in) < 0)
							err(1, "%s", input_file);
						return false;
					}
					v += (uint32_t)(c & 0x7f) << (exp++ * 7);
				} while ((c & 0x80) == 0);
				char *filename = malloc(v+1);
				if (!filename)
					err(1, "malloc");
				filename[v] = 0;
				if (fread(filename, 1, v, in) != v) {
					if (feof(in))
						warnx("%s: unexpected end of file", input_file);
					else
						warn("%s", input_file);
					free(filename);
					if (fclose(in) < 0)
						err(1, "%s", input_file);
					return false;
				}
				if (filename[0] != 0) {
					const char *p = strrchr(input_file, '/');
					if (!p)
						p = input_file;
					f = malloc(p - input_file + v + 1);
					if (!f)
						err(1, "malloc");
					memcpy(f, input_file, p - input_file);
					strcat(f, filename);
				}
				free(filename);
			}
		}
		if (!f) {
			f = strdup(input_file);
			if (!output_file)
				err(1, "strdup");
			size_t l = strlen(output_file);
			if (l >= 4 && f[l-3] == '.' && f[l-2] == 'b' && f[l-2] == 'r')
				f[l-3] = 0;
			else if (l >= 5 && f[l-4] == '.' && f[l-3] == 't' && f[l-2] == 'b' && f[l-2] == 'r')
				f[l-3] = 'a';
			else {
				warnx("%s: unknown suffix -- ignored", input_file);
				free(f);
				if (fclose(in) < 0)
					err(1, "%s", input_file);
				return false;
			}
		}
		int outfd = open(output_file, O_WRONLY | O_CREAT | (force ? O_TRUNC : O_EXCL), 0600);
		if (outfd < 0) {
			warn("%s", f);
			free(f);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		output_file = f;
		out = fdopen(outfd, "wb");
		if (!out) {
			warn("%s", output_file);
			free_global(&output_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			if (close(outfd) < 0)
				err(1, "%s", output_file);
			return false;
		}
	}
	if (nthreads == 1) {
		if (fseeko(in, 4, SEEK_SET) < 0) {
			warn("%s", input_file);
			goto fail;
		}
		if (!brzip_decompress1(input_file, to_stdout ? "stdout" : output_file, in, out))
			goto fail;
		if (fclose(in) < 0)
			err(1, "%s", output_file);
		if (!to_stdout) {
			if (fchmod(fileno(out), st.st_mode) < 0)
				warn("%s", output_file);
			if (futimens(fileno(out), times) < 0)
				warn("%s", output_file);
			if (fclose(out) < 0)
				err(1, "%s", output_file);
			free_global(&output_file);
			if (!keep && unlink(input_file) < 0)
				err(1, "%s", input_file);
		}
		return true;
	}
	if (fseeko(in, -1, SEEK_END) < 0) {
		warn("%s", input_file);
		goto fail;
	}
	int c = fgetc(in);
	while (c == 0) {
		if (fseeko(in, -2, SEEK_CUR) < 0) {
			warn("%s", input_file);
			goto fail;
		}
		c = fgetc(in);
	}
	if (c == EOF || (c & 0140) != 0040 || (0x34cb00 >> ((c ^ (c >> 4)) & 0xf) & 0x80)) {
		warnx("%s: corrupt input", input_file);
		goto fail;
	}
	if ((c & 020) == 0) {
		if (fseeko(in, 4, SEEK_SET) < 0) {
			warn("%s", input_file);
			goto fail;
		}
		if (!brzip_decompress1(input_file, to_stdout ? "stdout" : output_file, in, out))
			goto fail;
		if (fclose(in) < 0)
			err(1, "%s", output_file);
		if (!to_stdout) {
			if (fchmod(fileno(out), st.st_mode) < 0)
				warn("%s", output_file);
			if (futimens(fileno(out), times) < 0)
				warn("%s", output_file);
			if (fclose(out) < 0)
				err(1, "%s", output_file);
			free_global(&output_file);
			if (!keep && unlink(input_file) < 0)
				err(1, "%s", input_file);
		}
		return true;
	}
	switch (c & 7) {
		case 0:
		case 4:
			if (fseeko(in, -1, SEEK_CUR) < 0) {
				warn("%s", input_file);
				goto fail;
			}
			break;
		case 1:
		case 5:
			if (fseeko(in, -2, SEEK_CUR) < 0) {
				warn("%s", input_file);
				goto fail;
			}
			break;
		case 2:
		case 6:
			if (fseeko(in, -4, SEEK_CUR) < 0) {
				warn("%s", input_file);
				goto fail;
			}
			break;
		case 3:
			if (fseeko(in, -8, SEEK_CUR) < 0) {
				warn("%s", input_file);
				goto fail;
			}
	}
	int lastb = c;
	int64_t uncomp_len = -1;
	if (c & 010) {
		if (fseeko(in, -2, SEEK_CUR) < 0) {
			warn("%s", input_file);
			goto fail;
		}
		c = fgetc(in);
		if ((c & 0x80) == 0) {
			warnx("%s: corrupt input", input_file);
			goto fail;
		}
		uncomp_len = c & 0x7f;
		do {
			uncomp_len <<= 7;
			if (fseeko(in, -2, SEEK_CUR) < 0) {
				warn("%s", input_file);
				goto fail;
			}
			c = fgetc(in);
			uncomp_len |= c & 0x7f;
		} while ((c & 0x80) == 0);
	}
	if (fseeko(in, -2, SEEK_CUR) < 0) {
		warn("%s", input_file);
		goto fail;
	}
	c = fgetc(in);
	if ((c & 0x80) == 0) {
		warnx("%s: corrupt input", input_file);
		goto fail;
	}
	off_t offset = c & 0x7f;
	do {
		offset <<= 7;
		if (fseeko(in, -2, SEEK_CUR) < 0) {
			warn("%s", input_file);
			goto fail;
		}
		c = fgetc(in);
		offset |= c & 0x7f;
	} while ((c & 0x80) == 0);
	if (fseeko(in, -2, SEEK_CUR) < 0) {
		warn("%s", input_file);
		goto fail;
	}
	c = fgetc(in);
	if (c != lastb) {
		warnx("%s: corrupt input", input_file);
		goto fail;
	}
	offset_list_t offset_list = malloc(sizeof *offset_list);
	if (!offset_list)
		err(1, "malloc");
	offset_list->next = NULL;
	off_t trailer_offset = ftello(in) - 1;
	if (trailer_offset < 0) {
		warn("%s", input_file);
		goto fail;
	}
	for (;;) {
		if (offset == 0) {
			warnx("%s: corrupt input", input_file);
			goto fail;
		}
		if (offset > 1 << 26) {
			if (fseeko(in, 4, SEEK_SET) < 0) {
				warn("%s", input_file);
				goto fail;
			}
			if (!brzip_decompress1(input_file, to_stdout ? "stdout" : output_file, in, out))
				goto fail;
			if (fclose(in) < 0)
				err(1, "%s", output_file);
			if (!to_stdout) {
				if (fchmod(fileno(out), st.st_mode) < 0)
					warn("%s", output_file);
				if (futimens(fileno(out), times) < 0)
					warn("%s", output_file);
				if (fclose(out) < 0)
					err(1, "%s", output_file);
				free_global(&output_file);
				if (!keep && unlink(input_file) < 0)
					err(1, "%s", input_file);
			}
			return true;
		}
		if ((offset_list->off = (offset_list->next ? offset_list->next->off : trailer_offset) - offset) < 4) {
			warnx("%s: corrupt input", input_file);
			goto fail;
		}
		if (fseeko(in, offset_list->off, SEEK_SET) < 0) {
			warn("%s", input_file);
			goto fail;
		}
		c = fgetc(in);
		if (c == EOF) {
			warnx("%s: unexpected end of file", input_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		if ((c & 040) != 0) {
			warnx("%s: unexpected trailer", input_file);
			goto fail;
		}
		if (c == EOF || (0x34cb00 >> ((c ^ (c >> 4)) & 0xf) & 0x80)) {
			warnx("%s: corrupt input", input_file);
			goto fail;
		}
		if ((c & 020) == 0) break;
		offset = 0;
		unsigned exp = 0;
		do {
			if (exp * 7 >= sizeof(off_t) * 8)
				errx(1, "too long offset (at %uth byte)", exp);
			c = fgetc(in);
			if (c == EOF) {
				warnx("%s: unexpected end of file", input_file);
				if (fclose(in) < 0)
					err(1, "%s", input_file);
				return false;
			}
			offset += (off_t)(c & 0x7f) << (exp++ * 7);
		} while ((c & 0x80) == 0);
		offset_list_t offset_list_old = offset_list;
		offset_list = malloc(sizeof *offset_list);
		if (!offset_list)
			err(1, "malloc");
		offset_list->next = offset_list_old;
	}
	if (fseeko(in, 4, SEEK_SET) < 0) {
		warn("%s", input_file);
		goto fail;
	}
	courier_t ptr = brzip_start(0, nthreads, input_file, to_stdout ? "stdout" : output_file, out, decomp_worker, decomp_muxer);
	if (offset_list->off != 4) {
		size_t block_size = offset_list->off - 4;
		uint8_t *data = malloc(block_size);
		if (!data)
			err(1, "malloc");
		if (fread(data, 1, block_size, in) != block_size) {
			if (feof(in))
				warnx("%s: unexpected end of file", input_file);
			else
				warn("%s", input_file);
			brzip_finish(ptr);
			goto fail;
		}
		brzip_add_block(ptr, data, block_size);
	}
	while (offset_list) {
		off_t cur_offset = offset_list->off;
		offset_list_t offset_list_next = offset_list->next;
		free(offset_list);
		if (ptr->error)
			continue;
		size_t block_size = (offset_list_next ? offset_list_next->off : trailer_offset) - cur_offset;
		uint8_t *data = malloc(block_size);
		if (!data)
			err(1, "malloc");
		if (fread(data, 1, block_size, in) != block_size) {
			if (feof(in))
				warnx("%s: unexpected end of file", input_file);
			else
				warn("%s", input_file);
			brzip_finish(ptr);
			goto fail;
		}
		brzip_add_block(ptr, data, block_size);
		offset_list = offset_list_next;
	}
	if (!brzip_finish(ptr))
		goto fail;
	if (fclose(in) < 0)
		err(1, "%s", output_file);
	if (!to_stdout) {
		if (fchmod(fileno(out), st.st_mode) < 0)
			warn("%s", output_file);
		if (futimens(fileno(out), times) < 0)
			warn("%s", output_file);
		if (fclose(out) < 0)
			err(1, "%s", output_file);
		free_global(&output_file);
		if (!keep && unlink(input_file) < 0)
			err(1, "%s", input_file);
	}
	return true;

fail:
	if (fclose(in) < 0)
		err(1, "%s", output_file);
	if (!to_stdout) {
		if (fclose(out) < 0)
			err(1, "%s", output_file);
		if (unlink(output_file) < 0)
			err(1, "%s", output_file);
		free_global(&output_file);
	}
	return false;
}

static bool brzip_compress_stdin(uint8_t quality, uint32_t nthreads, uint32_t block_size) {
	courier_t ptr = brzip_start(quality, nthreads, "stdin", "stdout", stdout, comp_worker, comp_muxer);
	for (;;) {
		void *buf = malloc(block_size);
		if (!buf)
			err(1, "malloc");
		size_t l = fread(buf, 1, block_size, stdin);
		brzip_add_block(ptr, buf, l);
		if (feof(stdin))
			return brzip_finish(ptr);
		if (ferror(stdin)) {
			warn("stdin");
			brzip_finish(ptr);
			return false;
		}
		if (ptr->error) {
			char buf[0x1000];
			while (fread(buf, 1, sizeof(buf), stdin));
			brzip_finish(ptr);
			return false;
		}
	}
}

static bool brzip_compress_file(uint8_t quality, uint32_t nthreads, uint32_t block_size, const char *input_file, bool to_stdout, bool keep, bool force) {
	FILE *in = fopen(input_file, "rb"), *out = NULL;
	char filename[strlen(input_file) + 1];
	struct timespec times[2];
	if (!in) {
		warn("%s", input_file);
		return false;
	}
	struct stat st;
	if (to_stdout) {
		stat(input_file, &st);
		out = stdout;
	}
	else {
		size_t input_file_l = strlen(input_file);
		char *f = malloc(input_file_l + 4);
		lstat(input_file, &st);
		if (snprintf(f, input_file_l + 4, "%s.br", input_file) != (int)input_file_l + 3)
			err(1, NULL);
		int outfd = open(f, O_WRONLY | O_CREAT | (force ? O_TRUNC : O_EXCL), 0600);
		if (outfd < 0) {
			warn("%s", f);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
		output_file = f;
		out = fdopen(outfd, "wb");
		if (!out) {
			warn("%s", output_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			if (close(outfd) < 0)
				err(1, "%s", output_file);
			return false;
		}
		if (!out) {
			warn("%s", output_file);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			return false;
		}
	}
	courier_t ptr = brzip_start(quality, nthreads, input_file, to_stdout ? "stdout" : output_file, out, comp_worker, comp_muxer);
	ptr->filename = basename(strcpy(filename, input_file));
	ptr->timestamp = &st.st_mtime;
	times[0] = st.st_atim;
	times[1] = st.st_mtim;
	for (;;) {
		void *buf = malloc(block_size);
		size_t l = fread(buf, 1, block_size, in);
		brzip_add_block(ptr, buf, l);
		if (feof(in)) {
			if (!brzip_finish(ptr)) {
				if (fclose(in) < 0)
					err(1, "%s", input_file);
				if (!to_stdout) {
					if (fclose(out) < 0)
						err(1, "%s", output_file);
					if (unlink(output_file) < 0)
						err(1, "%s", output_file);
					free_global(&output_file);
				}
				return false;
			}
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			if (!to_stdout) {
				if (fchmod(fileno(out), st.st_mode) < 0)
					warn("%s", output_file);
				if (futimens(fileno(out), times) < 0)
					warn("%s", output_file);
				if (fclose(out) < 0)
					err(1, "%s", output_file);
				if (!keep && unlink(input_file) < 0)
					err(1, "%s", input_file);
				free_global(&output_file);
			}
			return true;
		}
		if (ferror(in)) {
			warn("%s", input_file);
			brzip_finish(ptr);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			if (!to_stdout) {
				if (fclose(out) < 0)
					err(1, "%s", output_file);
				if (unlink(output_file) < 0)
					err(1, "%s", output_file);
				free_global(&output_file);
			}
			return false;
		}
		if (ptr->error) {
			brzip_finish(ptr);
			if (fclose(in) < 0)
				err(1, "%s", input_file);
			if (!to_stdout) {
				if (fclose(out) < 0)
					err(1, "%s", output_file);
				if (unlink(output_file) < 0)
					err(1, "%s", output_file);
				free_global(&output_file);
			}
			return false;
		}
	}
}

void print_help() {
	fprintf(stderr, "usage: brzip [OPTION]... [FILE]...\nCompress or decompress FILEs in the .br format.\n\n"
		"  -c, --stdout        write on standard output, keep original files unchanged\n"
		"  -d, --decompress    decompress\n"
		"  -f, --force         force overwrite of output file\n"
		"  -h, --help          give this help\n"
		"  -k, --keep          keep (don't delete) input files\n"
		"  -0, --fast          compress faster\n"
		" -11, --best          compress better\n"
		" -B#, --block-size=#  split input data into blocks of size # (default: 4194304)\n"
		" -T#, --threads=#     compress using # working threads (default: number of processor threads)\n"
		"\n\nWith no FILE, or when FILE is -, read standard input.\n"
	);
}

void usage() {
	print_help();
	exit(1);
}

void on_interrupt() {
	if (output_file)
		unlink(output_file);
	exit(1);
}

int main(int argc, char **argv) {
	int level = 9;
	bool force = false;
	bool decompress = false;
	bool keep = false;
	bool opts_end = false;
	bool to_stdout = false;
	uint32_t block_size = 0;
	uint32_t nthreads = 0;
	const char *appname = strrchr(argv[0], '/');
	if (!appname++)
		appname = argv[0];
	if (tolower(appname[0]) == 'b' && tolower(appname[1]) == 'r') {
		if (tolower(appname[2]) == 'c' && tolower(appname[3]) == 'a' && tolower(appname[4]) == 't')
			to_stdout = decompress = true;
		if (tolower(appname[2]) == 'u' && tolower(appname[3]) == 'n' && tolower(appname[4]) == 'z' && tolower(appname[5]) == 'i' && tolower(appname[6]) == 'p')
			decompress = true;
	}
	for (int i = 1; i < argc; i++)
		if (argv[i][0] == '-' && argv[i][1] != 0 && !opts_end) {
			if (argv[i][0] == '-' && argv[i][1] == '-')
				switch (argv[i][2]) {
					case 0:
						opts_end = true;
						break;
					case 'b':
						if (!strcmp(argv[i] + 2, "best"))
							level = 11;
						else if (!strncmp(argv[i] + 2, "block-size", 10)) {
							block_size = 0;
							char *p = argv[i] + 12;
							if (*p == '=')
								p++;
							while (!*p) {
								i++;
								if (i == argc)
									usage();
								p = argv[i];
							}
							while (*p) {
								if (*p < '0' || *p > '9')
									usage();
								block_size = 10 * block_size + *p - '0';
								p++;
							}
						}
						else
							usage();
						break;
					case 'd':
						if (!strcmp(argv[i] + 2, "decompress"))
							decompress = true;
						else
							usage();
						break;
					case 'f':
						if (!strcmp(argv[i] + 2, "fast"))
							level = 0;
						else if (!strcmp(argv[i] + 2, "force"))
							force = true;
						else
							usage();
						break;
					case 'h':
						if (!strcmp(argv[i] + 2, "help")) {
							print_help();
							exit(0);
						}
						else
							usage();
						break;
					case 'k':
						if (!strcmp(argv[i] + 2, "keep"))
							keep = true;
						else
							usage();
						break;
					case 's':
						if (!strcmp(argv[i] + 2, "stdout"))
							to_stdout = true;
						else
							usage();
						break;
					case 't':
						if (!strncmp(argv[i] + 2, "threads", 7)) {
							nthreads = 0;
							char *p = argv[i] + 9;
							if (*p == '=')
								p++;
							while (!*p) {
								i++;
								if (i == argc)
									usage();
								p = argv[i];
							}
							while (*p) {
								if (*p < '0' || *p > '9')
									usage();
								nthreads = 10 * nthreads + *p - '0';
								p++;
							}
						}
						else if (!strcmp(argv[i] + 2, "to-stdout"))
							to_stdout = true;
						else
							usage();
						break;
					default:
						usage();
				}
			else {
				bool num = false;
				char *p = argv[i] + 1;
				while (*p) {
					if (*p >= '0' && *p <= '9') {
						level = num ? level * 10 + *p - '0' : *p - '0';
						num = true;
					}
					else {
						num = false;
						switch (*p) {
							case 'B':
								block_size = 0;
								p++;
								while (!*p) {
									i++;
									if (i == argc)
										usage();
									p = argv[i];
								}
								while (*p) {
									if (*p < '0' || *p > '9') {
										if (block_size)
											break;
										usage();
									}
									block_size = 10 * block_size + *p - '0';
									p++;
								}
								continue;
							case 'T':
								nthreads = 0;
								p++;
								while (!*p) {
									i++;
									if (i == argc)
										usage();
									p = argv[i];
								}
								while (*p) {
									if (*p < '0' || *p > '9') {
										if (nthreads)
											break;
										usage();
									}
									nthreads = 10 * nthreads + *p - '0';
									p++;
								}
								continue;
							case 'c':
								to_stdout = true;
								break;
							case 'd':
								decompress = true;
								break;
							case 'f':
								force = true;
								break;
							case 'k':
								keep = true;
								break;
							case 'h':
								print_help();
								exit(0);
								break;
							default:
								usage();
						}
					}
					p++;
				}
			}
		}
	opts_end = false;
	if (block_size == 0)
		block_size = 1 << 22;
	if (nthreads == 0)
		nthreads = get_nprocs();
	if (to_stdout)
		keep = true;
	bool from_stdin = true;
	bool error = false;
	struct sigaction sa_old, sa = { .sa_handler = on_interrupt, .sa_flags = 0 };
	sigaction(SIGINT, &sa, &sa_old);
	sigaction(SIGTERM, &sa, &sa_old);
	for (int i = 1; i < argc; i++) {
		if (argv[i][0] == '-' && argv[i][1] != 0 && !opts_end) {
			if (argv[i][1] == '-' && argv[i][2] == 0)
				opts_end = true;
		}
		else {
			from_stdin = false;
			if (argv[i][0] == '-' && argv[i][1] == 0)
				error |= decompress ? !brzip_decompress_stdin() : !brzip_compress_stdin(level, nthreads, block_size);
			else
				error |= decompress ? !brzip_decompress_file(nthreads, argv[i], to_stdout, keep, force) : !brzip_compress_file(level, nthreads, block_size, argv[i], to_stdout, keep, force);
		}
	}
	if (from_stdin)
		error = decompress ? !brzip_decompress_stdin() : !brzip_compress_stdin(level, nthreads, block_size);
	return error ? 1 : 0;
}

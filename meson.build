project('brzip', 'c', version: '0.2.1')

libbrotlienc = dependency('libbrotlienc')
libbrotlidec = dependency('libbrotlidec')
libxxhash = dependency('libxxhash')
if get_option('libmd')
	sha256 = dependency('libmd')
else
	sha256 = dependency('libcrypto')
endif
threads = dependency('threads')
deps = [libbrotlienc, libbrotlidec, libxxhash, sha256, threads]

if get_option('libmd')
	add_project_arguments('-DUSE_LIBMD', language: 'c')
endif

srcs = ['brzip.c', 'gsb_crc32.c']
if host_machine.cpu_family() == 'x86' or host_machine.cpu_family() == 'x86_64'
	srcs += ['crc32_sse42.c']
endif
brzip = executable('brzip', sources: srcs, c_args: '-D_FILE_OFFSET_BITS=64', dependencies: deps, install: true)

install_man('brzip.1')

meson.add_install_script('sh', '-c', 'NAME=$(basename @0@) ; ln -sf $NAME "$DESTDIR/@1@/@2@"/brcat${NAME#brzip}'.format(brzip.full_path(), get_option('prefix'), get_option('bindir')))
meson.add_install_script('sh', '-c', 'NAME=$(basename @0@) ; ln -sf $NAME "$DESTDIR/@1@/@2@"/brunzip${NAME#brzip}'.format(brzip.full_path(), get_option('prefix'), get_option('bindir')))

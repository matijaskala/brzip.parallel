project('brzip', 'c', version: '0.1')

libbrotlienc = dependency('libbrotlienc')
libbrotlidec = dependency('libbrotlidec')
libmd = dependency('libmd')
libxxhash = dependency('libxxhash')
threads = dependency('threads')
deps = [libbrotlienc, libbrotlidec, libmd, libxxhash, threads]

brzip = executable('brzip', 'brzip.c', 'gsb_crc32.c', c_args: '-D_FILE_OFFSET_BITS=64', dependencies: deps, install: true)

install_man('brzip.1')

meson.add_install_script('sh', '-c', 'NAME=$(basename @0@) ; ln -sf $NAME "$DESTDIR/@1@/@2@"/brcat${NAME#brzip}'.format(brzip.full_path(), get_option('prefix'), get_option('bindir')))
meson.add_install_script('sh', '-c', 'NAME=$(basename @0@) ; ln -sf $NAME "$DESTDIR/@1@/@2@"/brunzip${NAME#brzip}'.format(brzip.full_path(), get_option('prefix'), get_option('bindir')))

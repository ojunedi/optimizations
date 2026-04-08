#!/usr/bin/env zsh

# if argument is -h or --help, print usage
if [ $# -eq 1 ] && ( [ "$1" = "-h" ] || [ "$1" = "--help" ] ); then
    echo "Manually link and run assembly code with stub."
    echo "Usage: $0 <args>"
    exit 1
fi

os_type=$(uname -s)

if [ "$os_type" = "Darwin" ]; then
    format="macho64"
    extra_args="--target=x86_64-apple-darwin"
elif [ "$os_type" = "Linux" ]; then
    format="elf64"
else
    echo "unknown platform"
    exit 1
fi

nasm -f $format -o runtime/compiled_code.o runtime/compiled_code.s && \
ar rs runtime/libcompiled_code.a runtime/compiled_code.o && \
rustc runtime/stub.rs -C panic=abort -L runtime $extra_args -o runtime/stub.exe && \
./runtime/stub.exe "$@"

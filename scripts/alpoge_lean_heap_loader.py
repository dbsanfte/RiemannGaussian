"""Use the stock Lean 4.33.1 heap fallback for small compact files on Linux."""

import ctypes
import errno
import mmap
import os
import platform
import sys


class ArgumentComparison(ctypes.Structure):
    """The libseccomp scmp_arg_cmp ABI."""

    _fields_ = [("arg", ctypes.c_uint), ("op", ctypes.c_int),
                ("datum_a", ctypes.c_uint64), ("datum_b", ctypes.c_uint64)]


def checked(result: int) -> int:
    if result < 0:
        raise OSError(-result, os.strerror(-result))
    return result


def main() -> None:
    if sys.platform != "linux" or platform.machine() != "x86_64":
        sys.exit("The Alpöge compact-file loader requires x86-64 Linux.")
    if len(sys.argv) < 2:
        sys.exit("Expected a Lean executable and its arguments.")
    try:
        lib = ctypes.CDLL("libseccomp.so.2")
    except OSError as error:
        sys.exit(f"Cannot load libseccomp for --low-map-limit: {error}")
    lib.seccomp_init.argtypes = [ctypes.c_uint32]
    lib.seccomp_init.restype = ctypes.c_void_p
    lib.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
    lib.seccomp_rule_add_array.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int,
                                          ctypes.c_uint, ctypes.POINTER(ArgumentComparison)]
    lib.seccomp_load.argtypes = [ctypes.c_void_p]
    lib.seccomp_release.argtypes = [ctypes.c_void_p]
    lib.seccomp_release.restype = None

    # Lean first requests a fixed, private, writable file map. On ENOMEM its
    # own compact-region reader loads the same bytes on the heap and relocates them.
    map_fixed_noreplace = 0x100000
    private_fixed = mmap.MAP_PRIVATE | map_fixed_noreplace
    less_or_equal, equal, masked_equal = 3, 4, 7
    comparisons = (ArgumentComparison * 3)(
        ArgumentComparison(1, less_or_equal, 544 * 1024, 0),
        ArgumentComparison(2, equal, mmap.PROT_READ | mmap.PROT_WRITE, 0),
        ArgumentComparison(3, masked_equal, private_fixed | mmap.MAP_ANONYMOUS, private_fixed),
    )
    allow, return_errno = 0x7FFF0000, 0x00050000
    ctx = lib.seccomp_init(allow)
    if not ctx:
        raise MemoryError("Could not allocate a seccomp filter")
    try:
        syscall = checked(lib.seccomp_syscall_resolve_name(b"mmap"))
        checked(lib.seccomp_rule_add_array(ctx, return_errno | errno.ENOMEM, syscall,
                                           len(comparisons), comparisons))
        checked(lib.seccomp_load(ctx))
    finally:
        lib.seccomp_release(ctx)
    # Keep the fallback buffers on the ordinary glibc heap.
    os.environ["MALLOC_MMAP_MAX_"] = "0"
    os.environ["MALLOC_ARENA_MAX"] = "2"
    os.execvp(sys.argv[1], sys.argv[1:])


if __name__ == "__main__":
    main()

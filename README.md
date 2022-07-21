# RC

A C-like programming language implemented in Rust (for now)

> Now with [an official Hello, World program!](https://github.com/SatvikR/rc/blob/main/examples/helloworld.rc)

Compiles to x86-64 instruction set and uses linux syscalls. Expects both `nasm` and `ld` to be in `$PATH`.

## Example

> Calculates the 20th fibonacci number

```
i32 fib(i32 n) {
	if (n <= 1) return n;
	return fib(n - 1) + fib(n - 2);
}

i32 main() {
	i32 twentieth_fib = fib(20);
	return 0;
}
```

The language is **extremeley** minimal right now.

The only way to "output" anything right now is to use the syscall intrinsics as used in the hello world example.

> more examples in the example directory

## License

[BSD-2 Clause](https://github.com/SatvikR/rc/blob/main/LICENSE)

Copyright (c) 2022, Satvik Reddy

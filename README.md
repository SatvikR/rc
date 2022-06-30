# RC

A C-like programming language implemented in Rust (for now)

Compiles to x86-64 instruction set and uses linux syscalls. Expects both `nasm` and `ld` to be in `$PATH`.

## Example

> Calculates the 20th fibonacci number

```
i32 fib() {
	i32 calc = 20;
	i32 prev = 1;
	i32 curr = 0;
	i32 i = 1;
	while (i < calc) {
		i32 next = 0;

		next = prev + curr;
		prev = curr;
		curr = next;

		i = i + 1;
	}
	return curr;
}

i32 main() {
	i32 x = fib();
}
```

The language is **extremeley** minimal right now. There are no strings, characters,
standard library, etc.

The only way to "output" anything right now is to assign the value to a variable, and use
an external debugger like gdb to check the value of `rax`.

Nonetheless, it is turing complete.

## License

[BSD-2 Clause](https://github.com/SatvikR/rc/blob/main/LICENSE)

Copyright (c) 2022, Satvik Reddy

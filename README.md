# RC

A C-like programming language implemented in Rust (for now)

## Example: Fibonacci Number

```
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
curr = curr;
```

The language is **extremeley** minimal right now. There are no strings, characters,
functions, printing, etc. That last line (`curr = curr`) exists so that the compiler
forces the value of curr to be moved into the `rax` register.

The only way to "output" anything right now is to assign the value to a variable, and use
an external debugger like gdb to check the value of `rax`.

Nonetheless, it is turing complete.

## License

[BSD-2 Clause](https://github.com/SatvikR/rc/blob/main/LICENSE)

Copyright (c) 2022, Satvik Reddy

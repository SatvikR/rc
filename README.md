# RC

A C-like programming language implemented in Rust (for now)

> Check out [the official Hello, World program!](https://github.com/SatvikR/rc/blob/main/examples/helloworld.rc)

Compiles to x86-64 instruction set and uses linux syscalls. Expects both `nasm` and `ld` to be in `$PATH`.

## Example

```
i32 main() {
	puts("Hello, World\n");
	return 0;
}
```

> more examples in the example directory. Checkout the [sudoku solver example](https://github.com/SatvikR/rc/blob/main/examples/sudoku.rc) if you want to see a program that actually does something interesting

## License

[BSD-2 Clause](https://github.com/SatvikR/rc/blob/main/LICENSE)

Copyright (c) 2022, Satvik Reddy

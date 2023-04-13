# Meow lang

Meow lang is a programming language that compiles to *catlet*, another language that is hard to read but easy to execute. Meow's syntax is easier to read than catlet, but meow and catlet are equivalent.

The **only** operation is doing "let" (cat can be implemented by let).

Its main design purpose is to do experiments with "string substitution".

## Formal Definition

Currently the definition of substitution of strings are defined by the built-in `replace` function of `String`.

It's not allowed to do $[X/\epsilon]Y$ (replace empty string with some string).

## Concepts

There are **no** functions in Meow. Instead, we have *macros*. A macro is a piece of code that can be evaluated to a string.

The only available data type is **String**. (However, you can encode other data types inside String)

## Code Style

Meow:

```meow
encode(s) {
    var rep = {
        "$" = "\$";
        "#" = "\#";
        "\" = "\\";
        s
    };
    "#$"+ rep +"$#"
}

fib(x) {
    if(
        eq0(x),
        0(),
        if(
            leq(x, 2()),
            1(),
            add(
                fib(pred(x)),
                fib(pred(pred(x)))
            )
        )
    )
}
```

Catlet (Compiled result):

```catlet
encode s = cat cat "#$" let "$" "\$" let "#" "\#" let "\" "\\" s "$#"
fib x = if eq0 x 0 if leq x 2 1 add fib pred x fib pred pred x
```

## Simple Start

```bash
# First clone this repo and open it

cargo run repl

# Now you can use the REPL to evaluate (catlet) expressions
```

Example:

```
> "abc"
abc
> cat "hello " "world"
hello world
> let "apple" "world" "hello apple"
hello world
```

## Tutorials

- [Syntax](./docs/Syntax.md)
- [Encoding](./docs/Encoding.md)
- [Double Substitution Lemma](./docs/DSL.md)
- [Multiple Replacement](./docs/MR.md)

## Examples

See [syn.meow](./examples/syn.meow), which has compiled result [syn.cat](./examples/syn.cat).

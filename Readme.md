# Meow lang

Meow lang is a programming language that is designed **not** to be easy to learn and use.

Its main design purpose is to do experiments with "string replacement".

## Formal Definition

Currently the definition of replacement of strings are defined by the built-in `replace` function of `String`.

## Concepts

There are **no** functions in Meow. Instead, we have *macros*. A macro is a piece of code that can be evaluated to a string.

The only available data type is **String**. (However, you can encode other data types inside String)

## Simple Start

```bash
# First clone this repo and open it

cargo run ./examples/syn.meow

# Now you can use the REPL to evaluate expressions
```

Examples:

```
no error found.
> true()
T
> false()
F
> {var x = zero();succ(x)}
S0
> dr("a","aba","aba")
aba
> if("T","xsa","ddd")
xsa
> eq("as","asas")
F
```

## Tutorials

- [Syntax](./docs/Syntax.md)
- [Encoding](./docs/Encoding.md)
- [Double Replacement Lemma](./docs/DRL.md)

## Examples

See [syn.meow](./examples/syn.meow).

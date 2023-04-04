# Meow lang

Meow lang is a programming language that compiles to *cat*, another language that is hard to read but easy to execute. Meow's syntax is easier to read than cat, but meow and cat are equivalent.

Its main design purpose is to do experiments with "string substitution".

## Formal Definition

Currently the definition of substitution of strings are defined by the built-in `replace` function of `String`.

## Concepts

There are **no** functions in Meow. Instead, we have *macros*. A macro is a piece of code that can be evaluated to a string.

The only available data type is **String**. (However, you can encode other data types inside String)

## Simple Start

```bash
# First clone this repo and open it

cargo run repl

# Now you can use the REPL to evaluate (cat) expressions
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

## Examples

See [syn.meow](./examples/syn.meow), which has compiling result [syn.cat](./examples/syn.cat).

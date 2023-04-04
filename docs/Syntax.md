# Syntax

The layout of the whole language is not yet stable, but the core expression syntax is (relatively more) stable.

## Expression

**All expressions can be evaluated to a string literal.**

`Literal` is simply a string literal, like `"abc"`, `"lol"`.

There are two ways to define a string literal.

- "abc"
- \`abc\`

It's not allowed to use " inside a "-string and \` inside a \`-string.

Examples.

```meow
meow1() {
    "a" + "b"
}

meow2() {
    "a" = "b";
    "babaa"
}
```

`meow1` takes no argument, and it simply returns a string literal `"ab"`.

In `meow2`, we see that we have multiple "commands" in the curly bracket.

The syntax is like Rust, the last expression (which has no ";" at the end) in the block is the return value of the block.

`X;Y` means `let X in Y`, so `X;Y;Z` means `let X in (let Y in Z)`.

Different to many languages, `X=Y` requires that both `X` and `Y` are **expressions** (which is string).

`X=Y;Z` means that `let X=Y in Z`, which is $[Y/X]Z$ (string substitution).

`meow2` will return `"bbbbb"`.

The replacement **only** takes place in the `in xxx`. Hence, in `let X in (let Y in Z)`, the replacement of `X` only takes place in `Z` rather than `Y` (but there is a way to let it happen in `Y`, see later explanation).

`MacroApplication` is a macro name followed by a list of arguments, like `succ(a,b,c)`. The language is *by value*, so the arguments are evaluated before the macro is applied.

## Evaluation Mode

Evaluation has two modes. The **raw** mode and the **eval** mode.

In raw mode, a string literal will be simply be what it is. In eval mode, a string literal will be changed according to current rules in the context.

The **eval** mode is only used in the last expression in a block.

For example, consider the following macro:

```meow
meow() {
    "dd" = "d";
    var x = {"dddd"};
    var y = "dddd";
    "x=" + x + ", y=" + y
}
```

The rules will only apply to current context, it will not go into any deeper `{}` block.

The result of `meow()` is:

```
x=dd, y=dd
```

## Variable

You can use `var` to declare a variable. The syntax is like `var x = "abc";`. The variable is only visible in the block where it is declared. The right hand side can be any expressions. Note that the right hand side is evaluated in **raw** mode.

When compiling to cat, the compiler will **remove all `var` declarations**. So `var` is simply a **syntax sugar**.

For example,

```
meow() {
    "dd" = "d";
    var x = {"dddd"};
    var y = "dddd";
    x + y
}
```

will be compiled to:

```
meow  = let "dd" "d" cat "dddd" "dddd"
```

---

Til now, you may think that this language is very weak/useless. It turns out that it is really weak. But it can also do many interesting things.

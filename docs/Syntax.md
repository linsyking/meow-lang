# Syntax

The layout of the whole program is not stable, but the core expression syntax is (relatively more) stable.

## Expression

```
Expression ::=
            | Expression "+" Term
            | Term

Term ::=
      | Literal
      | MacroApplication
      | VarName
      | "{" BlockExpression "}"
      | "(" Expression ")"
```

**All expressions can be evaluated to a string literal.**

`literal` is simply a string literal, like `"abc"`, `"lol"`.

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

Different to many languages, `X=Y` requires that both `X` and `Y` are **expressions** (which is basically strings).

`X=Y;Z` means that `let X=Y in Z`, which is $[Y/X]Z$ (string replacement).

The replacement **only** takes place in the `in xxx`. Hence, in `let X in (let Y in Z)`, the replacement of `X` only takes place in `Z` rather than `Y` (but there is a way to let it happen in `Y`, see later explanation).

`MacroApplication` is a macro name followed by a list of arguments, like `succ(a,b,c)`. The language is *by value*, so the arguments are evaluated before the macro is applied.

## Evaluation Mode

Evaluation has two modes. The **raw** mode and the **eval** mode.

In raw mode, a string literal will be simply be what it is. In eval mode, a string literal will be changed according to current rules in the context.

For example, consider the following macro:

```meow
meow() {
    "dd" = "d";
    var x = {"dddd"};
    var y = "dddd";
    "x=" + x + ",y=" + y
}
```

Here `y` is raw mode evaluation while `x` is an eval mode evaluation. The thumb rule is that **only the last expression** in the block ({}) will be evaluated in eval mode.

Therefore, `x` is actually evaluated twice while `y` is evaluated only once.

The output of the code above:

```
x=d,y=dd
```

## Variable

You can use `var` to declare a variable. The syntax is like `var x = "abc";`. The variable is only visible in the block where it is declared. The right hand side can be any expressions. Note that the right hand side is evaluated in **raw** mode (unless you use `var x = {"abc"}`).

---

Til now, you may think that this language is very weak/useless. It turns out that it is really weak. But it can also do many interesting things.

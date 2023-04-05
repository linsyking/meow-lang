# Recursion

It's possible to do recursion **as long as** we use the *by name* catlet interpreter.

## Lazy (by name) evaluation

For example,

```meow
take(x) {
    "abc"
}

inf_loop() {
    inf_loop()
}

test() {
    take(inf_loop())
}
```

In the above code, `inf_loop` will be evaluated to itself. However, `take` will only evaluate `inf_loop` when it is used. So `test` will not cause infinite loop.

Moreover, the strict evaluation will not happen if the replacement is impossible. For example,

```meow
test() {
    "abc" = inf_loop();
    "xyz"
}
```

In the above code, `inf_loop` will not be evaluated because the replacement is impossible.

However, if you write the code like this:

```meow
test() {
    inf_loop() = "abc";
    "xyz"
}
```

This will cause infinite loop.

## Factorial

Now we can write factorial.

```meow
factorial(x) {
    if(
        eq(x, 1()),
        1(),
        mul(
            x,
            factorial(pred(x))
        )
    )
}
```

Compile result:

```catlet
factorial x = if eq x 1 1 mul x factorial pred x
```

## Fibonacci

```meow
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

Compile result:

```catlet
fib x = if eq0 x 0 if leq x 2 1 add fib pred x fib pred pred x
```

# Meow lang

Meow lang is a programming language that is designed to **not** be easy to learn and use.

Its mean design purpose is to do experiments with "string replacement".

## How to run

```bash
cargo run <your meow file path>

# Now you can use the REPL to evaluate expressions
```

Run the example code:

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
> m()
abcd
```

## Examples

```meow
true() {"T"}

false() {"F"}

zero() {"0"}

succ(x) {"S"+x}

pred(x) {
    "S0" = "0";
    x
}

dr(x,y,z) {
    y = x;
    x = y;
    z
}

rep_test() {
    "dd" = "d";
    var x = {"dddd"};
    var y = "dddd";
    "x=" + x + ",y=" + y
}

encode(s) {
    var rep = {
        "\" = "\\";
        "$" = "\$";
        "^" = "\^";
        s
    };
    "_^"+ rep +"_$"
}

decode(s) {
    var rep = {
        "_^" = "";
        "_$" = "";
        s
    };
    "\$" = "$";
    "\^" = "^";
    "\\" = "\";
    rep
}

m(){
    var s = "abcd";
    var enc = encode(s);
    var dec = decode(enc);
    dec
}
```

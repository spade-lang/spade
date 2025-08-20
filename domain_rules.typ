#import "@preview/curryst:0.5.1": rule, prooftree

#let dom_const = `'const`
#let checks = sym.arrow.double.l

#let name(name) = {
  set text(fill: gray)
  name
}

#show sym.arrow.double: set text(fill: orange)
#show sym.arrow.double.l: set text(fill: blue)

#let expr(content) = {
  set text(fill: purple)
  content
}

We have the following domains
- `'const`: Any constant value. Can be put anywhere
- `'async`: A value with no associated clock, cannot be stored in registers
- `T`: a named domain. Two named domains cannot be mixed unless there is an explicit `T1 <: T2` constraint
- $(t_1, t_2)$: a tuple. Things are a lot easier to reason about if we only have two-tuples so we'll have to do some conversion of `n`-tuples in the domain inferer
- $t_1 -> t_2$: Function from one domain to another

This is something we should account for when we do more complex pipelines
- `enabled(`$t_1$`)`: A domain with the same clock as $t_1$ but with a more restrictive enable.

In addition, we need to have constraints
  - `!SyncReset`
  - `!AsyncReset`
  - `!Initial`
  - `!Enable`

The default domain unless anything else is specified is {}. A unit or language construct can refine this with constraints

#let subtyping_rules = (
  const:  ([`'const` $<: t_1$]),
  async: ([$t_1 <: $ `'async`]),
  // // I don't like these rules...
  // ltuple: ([$(t_1, t_2) <: t_1$], $t_2 <: t_1$),
  // rtuple: ([$(t_2, t_1) <: t_1$], $t_2 <: t_1$),
  tuple_sub: ($Gamma tack (t_1, t_2) <: t_3$, $Gamma tack t_3 : min(t_1, t_2)$),
  constraints: (
    $Gamma tack t_1 <: t_2$,
    $Gamma tack t_1{c_1...c_n}$,
    $Gamma tack t_2{c_1,...c_n, d_1...}$)
  
)

#let rules = (
  literal: (
    $expr(#`0`) : #dom_const$
  ),
  name: (
    $Gamma tack x : t_1$,
    $t_1 = #`lookup` (Gamma, x)$,
  ),
  tuple_union: (
    $Gamma tack.r expr((e_1, e_2)): (t_1, t_2)$,
    $Gamma tack.r expr(e_1) : t_1$,
    $Gamma tack.r expr(e_2): t_2$
  ),
  clock_requirement: (
    $expr("reg" x = e_2), #`extend` (Gamma, x in t_1)$,
    $Gamma tack expr(e_1) : t_1$,
    $Gamma tack #`has_clock(` t_1#`)`$ 
  ),
  binop: (
    $Gamma tack expr(e_1 xor e_2) : t_1$,
    $Gamma tack e_1 : t_1$,
    $Gamma tack e_2: t_1$
  ),
  "set": (
    $Gamma tack expr("set" e_1 = e_2), t_2 <: t_1$,
    $Gamma tack e_1: t_2$,
    $Gamma tack e_2: t_u$
  )
)

#let bidir_rules = (
  literal: $expr(0) checks #dom_const$,
  name: ($Gamma tack x => t$, $t_1 = "lookup"(Gamma, x)$),
  tuple_union: (
    $Gamma tack expr((e_1, e_2)) => (t_1, t_2)$,
    $Gamma tack expr(e_1) => t_1$,
    $Gamma tack expr(e_2) => t_2$
  ),
  clock_requirement: (
    $expr("reg" x = e_1), #`extend` (Gamma, x in t_1) $,
    $Gamma e_1 => t_1$,
    $Gamma tack x checks #`has_clock` (t_1)$
  ),
  binop: (
    $Gamma tack expr(e_1 xor e_2) => t_1$,
    $Gamma tack e_1 => t_1$,
    $Gamma tack e_2 checks t_1$,
  ),
)


#let draw_rule(name, inner) = {
  if type(inner) == array {
    prooftree(rule(name: text(fill: gray, name), ..inner))
  } else {
    prooftree(rule(name: text(fill: gray, name), inner))
  }
}
#let draw_rule_pair(name, inner) = {
  let bidir_variant = bidir_rules.at(name, default: none) 
  let main = box(draw_rule(name, inner))
  let bidir = box(if bidir_variant != none {
    draw_rule(name, bidir_variant)
  })

  context {
    layout(avail => {
      let main_size = measure(main)
      box(width: calc.max(avail.width/2, main_size.width), main)
      if main_size.width > avail.width / 2 {
        linebreak()
        align(right, bidir)
      } else {
        bidir
      }
      linebreak()
      v(0.4em)
    })
  }
}

= Subtyping rules

#for (name, inner) in subtyping_rules {
  draw_rule_pair(name, inner)
}



= Normal rules

#for (name, inner) in rules {
  draw_rule_pair(name, inner)
}


= The tuple issue

This should domaincheck
```spade
entity test<'a, 'b>(a: 'a T1, b: 'a T2) {
  reg x = (a, b);
}
```
and this
```spade
entity test<'a, 'b>(a: 'a T1, b: 'a T2) {
  reg x = (a, 0);
}
```
This should not
```spade
entity test<'a, 'b>(a: 'a T1, b: 'b T2) {
  reg x = (a, b);
}
```

Case one should be fairly simple, we want to show `x: 'a`

#prooftree(
  rule(
    name: name("tuple_sub"),
    $expr((a, b)) : 'a$,
    rule(
      name: name("tuple_union"),
      $Gamma tack expr((e_1, e_2)) : ('a, 'a)$,
      rule(
        $expr(a) : 'a$,
        rule(
          name: name("name"),
          $#`lookup` (Gamma, a)$
        )
      ),
      rule(
        $expr(b) : 'a$,
        rule(
          name: name("name"),
          $#`lookup` (Gamma, a)$
        )
      ),
    )
  )
)

Case 2 `(a, 0)`

#prooftree(
  rule(
    name: name("tuple_sub"),
    $Gamma tack expr((a, 0)): 'a$,
    rule(
      name: name("tuple_union"),
      $Gamma tack expr((a, b)) : ('a, #`'const`)$,
      rule(
        name: name("name"),
        $Gamma tack expr(a) : 'a$,
        $Gamma tack #`lookup` (Gamma, a)$
      ),
      rule(
        name: name("const"),
        $Gamma tack expr(0) : #`'const`$,
      ),
    ),
  )
)

The final path fails for the `(a, b)` case, because `tuple_sub` requires the subtyping judgement

= Set

`a: T, b: 'async; set a = b` is not allowed

#prooftree(
  rule(
    name: name("set"),
    $Gamma cancel(tack) expr("set" a = b), #`'async` cancel(<:) T$,
    rule($a: T$),
    rule($b: #`'async`$),
  )
)
#sym.square

= Issues

`has_clock` feels sketchy, essentially i'm imagining this:
```rust
match t {
  'async => false,
  // We could go with false here too, but we can fall back on the annonymous
  // later domain to allow `reg x = x + 1;` without specifying the domain
  'const => true, 
  // Named types must have a HasClock constraint which is implicit unless otherwise
  // stated
  T => T.constraints.contains(HasClock),
  // Tuples have a clock if t1 and t2 are in compatible domains. For example
  // (a, 0) can be registered but its domain is (t_1, 'const). Therefore we need
  // a subtyping thing here.
  (t1, t2) => {
    let domain = min(t1, t2); // The smallest subdomain that contains both t1 and t2
    has_clock(domain)
  }
}
```

= Just a normal type system with weird subtyping rules

What if we just steal the type system from #link("https://arxiv.org/pdf/1908.05839") with our subtyping rules and desugaring of our interesting constructs to lambda calculus.

*Nope* Tuple constructors are weird functions

Operators can be de-sugared to

$
  ((lambda o_a: t_1. (lambda o_b: t_1 . o_a)) a) b
$

From which we can derive
#prooftree(
  rule(
    name: name($->E=>$),
    $expr(((lambda o_a: t_1. (lambda o_b: t_1 . o_a)) a) b) => t_1$,
    rule(
      name: name($->E=>$),
      $Gamma tack expr((lambda o_a: t_1. (lambda o_b: t_1 . o_a)) a) => t_1 -> t_1$,
      rule($Gamma tack expr(lambda o_a: t_1. (lambda o_b: t_1 . o_a)) => t_1 -> t_1$, [This is given by the operator]),
      rule($Gamma tack expr(a) checks t_1$)
    ),
    rule(
      $Gamma tack expr(b) checks t_1$
    ),
  )
)

Therefore, we can add a rule that says.

#prooftree(rule(
  $Gamma tack expr(e_1 xor e_2) => t_1$,
  $Gamma tack e_1 checks t_1$,
  $Gamma tack e_2 checks t_1$,
))

Or wait, can we? We don't have annotations for $t_1$. In the least helpful sense, the operator signature is really and then we suddenly need polymorphism 😢
$
  forall alpha ((lambda o_a: alpha. (lambda o_b: alpha . o_a)) a) b
$


A much more sane solution is probably to simply change it to,
#prooftree(rule(
  $Gamma tack expr(e_1 xor e_2) => t_1$,
  $Gamma tack e_1 => t_1$,
  $Gamma tack e_2 checks t_1$,
))

Can we do the same with set statements? The slightly troubling part is that these do not really have an output type, they constrain the inputs. Is this closer to a variable introduction?
$
  ((lambda o_a: t_1. (lambda o_b: t_1 <: t_2 . o_a)) a) b
$


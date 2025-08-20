#import "@preview/curryst:0.5.1": rule, prooftree

#let name(name) = {
  set text(fill: gray)
  name
}


#let expr(content) = {
  set text(fill: blue)
  content
}

These domains exist
- `'const`: Any constant value. Can be put anywhere
- `'async`: A value with no associated clock, cannot be stored in registers
- `T`: a named domain. Two named domains cannot be mixed unless there is an explicit `T1 <: T2` constraint
- $(t_1, t_2)$: a tuple. Things are a lot easier to reason about if we only have two-tuples so we'll have to do some conversion of `n`-tuples in the domain inferer
- $t_1 -> t_2$: Function from one domain to another
This is something we should account for for pipelines
- `enabled(`$t_1$`)`: A domain with the same clock as $t_1$ but with a more restrictive enable.

#let subtyping_rules = (
  const:  ([`'const` $<: t_1$]),
  async: ([$t_1 <: $ `'async`]),
  // // I don't like these rules...
  // ltuple: ([$(t_1, t_2) <: t_1$], $t_2 <: t_1$),
  // rtuple: ([$(t_2, t_1) <: t_1$], $t_2 <: t_1$),
  tuple_sub: ($(t_1, t_2) <: min(t_1, t_2)$)
)
#let rules = (
  tuple_union: (
    $Gamma tack.r expr((e_1, e_2)): (t_1, t_2)$,
    $Gamma tack.r expr(e_1) : t_1$,
    $Gamma tack.r expr(e_2): t_2$
  ),
  clock_requirement: (
    $expr("reg" x = e_2), Gamma, x in t_1$,
    $Gamma tack expr(e_1) : t_1$,
    $Gamma tack #`has_clock(` t_1#`)`$ 
  ),
  binop: (
    $Gamma tack expr(e_1 xor e_2) : t_1$,
    $Gamma tack e_1 : t_1$,
    $Gamma tack e_2: t_1$
  ),
  unop: ($Gamma tack expr(xor e_1) : t_1$, $Gamma tack expr(e_1) : t_1$),
)


#let draw_rule(name, inner) = {
  if type(inner) == array {
    prooftree(rule(name: text(fill: gray, name), ..inner))
  } else {
    prooftree(rule(name: text(fill: gray, name), inner))
  }
}

= Subtyping rules
#for (name, inner) in subtyping_rules {
  draw_rule(name, inner)
}

= Normal rules
#for (name, inner) in rules {
  draw_rule(name, inner)
}

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

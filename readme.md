# My Attempt at System Fω with Row-Polymorphism

As I worked on trying to build my own functional programming language, I ended
up going really deep down the research rabbit hole and decided I want to focus
on trying to understand how System-Fω works and how it can compile to machine
code.

This project is my attempt at implementing some form of it based on my patched
together understanding from various papers and books I've found during my
research. It's not going to be complete, and it will very likely be full of
bugs, but I'm hoping I can eventually implement some kind of abstract machine
with call-by-value semantics.

I'll be attempting to add row-polymorphism as described by the
[Extensible records with scoped labels](https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/)
paper by Daan Leijen. I hope to eventually be able to implement some kind of
module system on top of it, and maybe even some kind of 'modular implicits' akin
to the [infamous OCaml proposal](https://arxiv.org/abs/1512.01895).

Once I have some real machine code being generated, I'll likely focus on
building an inferred language on top of it, but that's a while to go…

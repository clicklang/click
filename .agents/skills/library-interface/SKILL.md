---
name: library-interface
description: Add or change Click's support for a library function or type the verified code calls, in C, C++ or Rust — a standard-library or core function, method or type, such as "add support for `Vec::pop`", "support `std::string`", "handle `memmove`", "make `Option::take` work". Use before writing any code for it, and whenever a library call is refused or special-cased.
---

# Library interface

The rules are in `docs/concepts/library-interfaces.md`. Read it first. This
skill is the procedure for applying them.

## Before writing code

1. Name what is being added: the library function, method or type, its
   language, and the call a program makes.
2. Check it is a library interface, not a language primitive. C pointers,
   Rust references and slices, and steps the compiler builds in are lowered
   by the front end; everything a library provides is an interface.
3. Look up the "Where the implementation departs from this" table on that
   page. If the item is listed there, the work replaces that special case;
   do not extend it.

## Writing it

1. State the contract, and the type's ownership resource if it owns
   memory, in `library/c/`, `library/cpp/` or `library/rust/`. Describe
   observable state and effects: logical values, what is owned, preconditions,
   effects and invalidation. Never the representation or the implementation.
2. Map the call to the contract in the front end's name table, and nothing
   else. No front-end rewrite of what the library does.
3. Add the inventory item, the library reference entry and the trust row.
4. Add a verified use that calls it and verifies, and a case where an unmet
   precondition is refused.

## When a contract cannot say it

Stop. Describe to the user what the contract needs that contracts or
resources cannot express, with the smallest example, and propose the general
fix. Do not add a special case to get past it.

## In the PR

Say which steps were done, and if the work replaced or added a row of the
departures table, update the table.

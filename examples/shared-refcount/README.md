# Shared reference count across threads

This synthetic C11/POSIX program shares one reference-counted object between
its owner and two user threads. The owner allocates the object with one
reference, initializes its mutex, and retains one more reference for each
user under the mutex before creating that user's thread. Each user releases
its reference under the mutex. After both users have been joined, the owner
releases its own reference, destroys the mutex, and frees the object.
`run` joins the users in creation order and `run_reverse_join` in the other
order; both cover a failed first or second `pthread_create`. The project uses
the `x86_64-linux-userspace` target, the explicit `modeled-pthread` runtime,
and authority resource semantics.

## Proof shape

`control(obj)` is the resource the mutex holds. It owns the counter cell and
the authorities of two populations: `reference(obj)` for the references and
`permit(obj)` for unused retain capacity. Its facts tie the counter to the
reference count and state the cap: references plus permits always equal 3.
`object_retain` consumes a permit and produces a reference;
`object_release` consumes a reference and produces a permit. Each locks the
mutex, opens the control under a fresh total, makes exactly that exchange,
and restores the control before unlocking.

The cap is what makes the plain `refs = refs + 1` safe. A retain holds a
permit, so at least one unit of capacity is unused and the counter is at
most 2 before the increment. Nothing in the C enforces the cap; it is a
stated bound that the proof carries, and the owner creates two permits at
initialization, one for each retain it will make. Without it the increment
is refused for possible signed overflow
(`mdtests/authority_mutex_locked_retain_without_cap_rejected.md`).

Each user is a `pthread_create` worker that borrows a typed `mutex_use`
share and calls `object_release` without locking itself. Both users may be
outstanding at once: creation leaves the populations in the mutex, and each
join applies that user's checked exchange. Until both have joined, the owner
cannot observe either population's total. After the joins and its own
release, the owner destroys the mutex, recovers the control, spends the three
permits, observes both totals at zero, retires both authorities, and frees
the object.

The runtime assumption covers the modeled mutex and create/join operations;
this proof does not validate a native pthread implementation. The C source is
pinned in `tests/examples.rs`.

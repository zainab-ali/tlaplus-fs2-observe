# TLA+ and fs2

This repository is an attempt at modelling some of fs2's behaviour in
TLA+. It aims to verify that some of the concurrent code behaves as
we'd like it to.

Specifically, I want to verify that the implementation of `observe` is
correct, and that [I can simplify it](https://github.com/typelevel/fs2/issues/2778
). I'm concerned that the refactored code might contain race
conditions, or different behaviour, but can't work this out by eye.

## Learning TLA+
I've been using the [Learn TLA+ website](https://www.learntla.com/introduction/), written by Hillel,
and have recorded my progress in `~/record/tlaplus`. The `~/tlaplus`
directory contains examples used in the website.

## Prior Art

The easiest model for reasoning about `fs2` is CSP. For example, the
following code can be split into processes:

```scala
Stream(1,2,3)   // Process UPSTREAM
.evalTap(
  q.enqueue     // Process QUEUE
)
.concurrently(  // Process DOWNSTREAM
  q.dequeue     // Process QUEUE
)
.compile.drain
```

The messages sent between these processes are requests, responses and
cancellations. fs2's `uncons` can be thought of as a `request` message
sent from `DOWNSTREAM` to `MID`, and it's result as a `response`
message sent from `MID` to `DOWNSTREAM`. The `evalTap` performs a
`Pull.eval`, which can be thought of as a `start eval` and `stop eval`
message sent between `MID` and `QUEUE`.

Note that the `UPSTREAM` and `DOWNSTREAM` processes can probably be
combined into a single process that communicates with `QUEUE`, however
it is then harder to see the parallels between this combined process
and the original code.

Edwin Brady has a paper on encoding CSP rules in Idris that may be
helpful, should I try and encode this reasoning using a dependently
typed Finite State Machine. However, I'll start with TLA+ and see
where I end up.

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

## Prior Art on CSP

Note that CSP has a different method of reasoning to that presented in
TLA+. I'm including this prior art as food for thought.

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

# Phrasing the problem

Phrasing a problem in TLA+ seems to be a step-by-step process:
 1. Identify the **properties** of the system. 
    
	These are the invariants. For example ”all elements that were
    pulled from upstream must have been requested”.

 2. Identify the **steps** of the computation.
 
    These are the atomic units that the evaluator can take when
    interleaving the code. Think “If this was a co-routine, where
    would it yield?”.
	
 3. Model the **state** that is changed at each step.

    Creating a decent model is somewhat of an art. The primitive types
    of TLA+ aren’t too similar to a usual programming language.

I expect that the yield points will be the most tricky to identify. It
would be easy to spec out an incorrect model of the way fs2 works by
mis-identifying its yield points.
	

# Identifying yield points

The yield points are dependent on the fs2 `Pull` interrupt semantics,
as defined in the pull `compile` function, and the cats-effect `race`
semantics.

To simplify things, we can assume that a program can yield at every
`flatMap`, and that `race` polls a completion flag for two
operations.

# Iterating the code

A naive attempt at `observe` would be:

```scala
upstream
  .evalMap(q.enqueue)
  .concurrently(q.dequeue.through(pipe))
```

There are a few problems with this implementation:
 - It does not terminate if the `pipe` requests fewer elements than
   are pulled by the output stream
 - The pipe is cancelled nondeterministically (sometimes the left stream terminates first).

These can both be identified by TLA+.

The next attempt should tackle the cancellation.

```
upstream.evalMap(q.enqueue)
  .concurrently(q.dequeue.through(pipe))
  
// Only when the upstream terminates do we close the queue
q.dequeue
  .concurrently(
  upstream.evalTap(q.enqueue).through(pipe) ++ q.close
  )
```

It would be worth writing some library code for:
 - the `q.dequeue` process
 - the `evalTap(q.enqueue)` process

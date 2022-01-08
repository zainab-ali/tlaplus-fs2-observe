# TLA+ and fs2

This repository is an attempt at modelling some of fs2's behaviour in
TLA+. It aims to verify that some of the concurrent code behaves as
I'd like it to.

Specifically, I want to verify that the implementation of `observe` is
correct, and that [I can simplify it](https://github.com/typelevel/fs2/issues/2778
). I'm concerned that the refactored code might contain race
conditions, or different behaviour, but can't work this out by eye.

## Learning TLA+
I've been using the [Learn TLA+ website](https://www.learntla.com/introduction/), written by Hillel,
and have recorded my progress in `~/record/tlaplus`. The `~/tlaplus`
directory contains examples used in the website.

Following that, I have skimmed through [Leslie Lamport's video tutorials](https://www.youtube.com/channel/UCajiu4Cj_GHOX0if3Up-eRA).

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

```
upstream.evalMap(q.enqueue)
  .concurrently(q.dequeue.through(pipe))
  
// Only when the upstream terminates do we close the queue
(sem.release > q.dequeue)
  .concurrently(
  upstream.evalTap(sem.acquire >> q.enqueue).through(pipe) ++ q.close
  )
```

enqTakeN = deqTakeN => enqRecEls = deqRecEls

empty observer == empty output

- If the observer raises an error, then that error should be propagated downstream
- If the source raises an error, then that error should be propagated downstream
- If any errors are raised, then the streams should terminate

We should now model errors.

# Properties of `observe`

Consider

```
output = input.observe(pipe)
```

I think any implementation of `observe` should satisfy:
 - If `input` is finite, then `output` terminates
 - If the `input` terminates with an error, then the `output` terminates with an error
 - If the `observer` terminates with an error, then the `output` terminates with an error
 - No more elements are pulled from `input` than are requested by `output`
 - An element is only pulled from `input` if both `observer` and `output` request it
 - The number of elements pulled from `input` is at most one greater than the number of elements requested by `output`
 - If the `input` is finite and the `observer` requests the same number of elements as the `output`, then the `output` and `observer` should both complete.
 - If the `observer` requests more elements than the `output` then it should be cancelled. 
 - If the `output` terminates successfully, then the elements pulled by it should be equal to those pulled from `input`
 - If the `observer` terminates successfully, then the elements pulled by it should be equal to those pulled from `input`
 - If the `observer` cancels itself, then the `output` is cancelled 
 - If the `output` cancels itself, then the `observer` is cancelled. 

*NOTE* According to the `observe` tests, the `observer` can possibly be one element ahead of the output:

```scala
group("handle finite observing sink") {
  test("2") {
    forAllF { (s: Stream[Pure, Int]) =>
      observer(Stream(1, 2) ++ s.covary[IO])(_.take(1).drain).compile.toList
        .assertEquals(Nil)
    }
  }
}
```

## The state

In order to assert these properties, we need:
 - A state of `Completed`, `Cancelled`, `Running` and `Errorred` that can be applied to the `input`, `observe` and `output`
 - The sequence of elements pulled from `input`
 - The number of elements requested by `output`
 - The number of elements requested by `observer`
 - The sequence of elements received by `output`
 - The sequence of elements received by `observer`
 
We can represent this as

```
state \E { S_running, S_completed, S_cancelled, S_errored }
P \E { P observer, P_output, P_input }
el \E {Nat}
stream[P].nRequested \E <<el>>
stream[P].received \E <<el>> \* Note that stream[P_input].received doesn't make any sense. We could use it to represent the set of elements to pull downstream.
stream[P].sent \E <<el>>
```

We must also configure:
 - An `infinite` boolean value, indicating if `input` is infinite
 - The number of elements to be requested by `output`
 - The number of elements to be requested by `observer`
 - The sequence of elements to be sent by `input`
 - Whether the `input` should terminate with an error
 - The element index at which the `observer` should terminate with an error, if any
 - The element index at which the `output` should terminate with an error, if any
 - The element index at which the `observer` should terminate with a cancellation, if any
 - The element index at which the `output` should terminate with a cancellation, if any

```
stream[P].NMaxRequests \E ({INF} \U Nat)
stream[P].terimation = { T_Normal, T_Error, T_Cancel}
```

This model is slightly more complex than we need to represent all of
the invariants. However, it does generalize nicely to different stream
components (the same state structure can be used for input, output and
observe). 

Most of the invariants can be expressed, except for:
 - [ ] If `in` is finite, then `out` terminates
 - [ ] If the `in` is finite and the `observer` requests the same number of elements as the `out`, then the `out` and `observer` should both complete.


TODO: Can we have a stream.take(0) ?

Is an error in self different to an error in observer?

in.onFinalize(x)
.observe(observer)

is different to in.observe(observer), but do we need to care?

Does an in cancellation propagate downstream?
Yes.

There are a couple of cases to explore here:
 - the observer is unrelated to the input
 - the observer is a direct pull of the input

It isn't possible to take(0), so the model should reflect this.

Next steps:
 - try and design the previous runner to have a sequential mode
 - add an assume clause with an output minimum take of 1

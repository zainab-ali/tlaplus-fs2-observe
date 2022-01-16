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

## A naive observe implementation

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

## An observe implementation with cancellation

The following code ensures that the observer isn't cancelled:

```scala
upstream.evalMap(q.enqueue)
  .concurrently(q.dequeue.through(pipe))
  
// Only when the upstream terminates do we close the queue
q.dequeue
  .concurrently(
  upstream.evalTap(q.enqueue).through(pipe) ++ q.close
  )
```

# Thoughts

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
 - A state of `Succeeded`, `Cancelled`, `Running` and `Errorred` that can be applied to the `input`, `observe` and `output`
 - The sequence of elements pulled from `input`
 - The number of elements requested by `output`
 - The number of elements requested by `observer`
 - The sequence of elements received by `output`
 - The sequence of elements received by `observer`
 
We can represent this as

```
state \E { SRunning, SSucceeded, SCancelled, SErrored }
P \E { PObserver, POutput, PInput }
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
stream[P].nTake \E ({INF} \U Nat)
stream[P].terimation = { TNormal, TError, TCancel}
```

This model is slightly more complex than we need to represent all of
the invariants. However, it does generalize nicely to different stream
components (the same state structure can be used for input, output and
observe). 

Most of the invariants can be expressed, except for:
 - [ ] If `in` is finite, then `out` terminates
 - [ ] If the `in` is finite and the `observer` requests the same number of elements as the `out`, then the `out` and `observer` should both complete.

# Thoughts on Assumptions

The output must request at least one element for the system to run. This puts a lower bound of 1 on `out.nTake`.

The observer scope may have any sort of relationship to the input scope. This makes error propagation and cancellation difficult to model, as these are dependent on the scope relationship. We will classify the relationship as one of:
 - `OParent`, implying that the observer is a parent of the input. For example, `observer = _.take(3)`
 - `OTransient`, implying that the observer is a parent of the input at some point in time. For example `observer = _ ++ other`
 - `ONone`, implying that the input and observer scopes are unrelated. The input may run concurrently to the observer. We have to assume certain error propagation behaviours in this case.
 
The observer may handle errors in the input with `handleErrorWith`, thus the observer termination state doesn't necessarily reflect the input termination state.

# Thoughts on cancellation

Cancellation is performed through an interrupt that is raced at each task.
 - How do interrupts work with concurrently? If we interrupt the output stream, how is the background cancelled?

Cancellation occurs when a stream is started in a different fiber, and that fiber is cancelled.

If the observer stream doesn't fork the input stream, then the input stream is cancelled exactly when the observer stream is cancelled.
If the observer stream forks the input stream, then the observer stream may be cancelled, and may decide to cancel the input stream.

When the observer stream terminates, via cancellation or otherwise, it may decide to cancel

# Assumptions

 1. The effect that creates the `observe` system and starts it concurrently is only created if an element is pulled downstream. Thus, the `out` stream must pull at least one element.
 
	If the system could be started without the output requesting an element then some invariants would be violated, notably the invariants that relate the elements pulled from the input to those received by the output.

 2. The `observer` pipe must clean up resources on the `in` stream. A well-behaved observer must not start the `in` stream in a fiber and forget to cancel it.
 
   This assumption affects the order of steps following `onFinalize(channel.close)`. The `in` stream cannot take steps after the channel has been closed.

 3. The `observer` may run the `in` stream concurrently to itself. Elements may be pulled from the `in` stream independently of any work done in the observer. The `observer` may also cancel the `in` stream while it itself completes successfully.
 
 If the `observer` stream is cancelled, then it must cancel the `in` stream. It does so before closing the channel with `onFinalize(channel.close)`.
 


# Understanding Cancellation

PlusCal introduces the idea of a process - a series of sequential steps. Processes run independently of each other, meaning that they can interleave their steps. 

Streams are sequential by default, so a stream system should be modelled as a single process. This makes streams difficult to map to PlusCal code as their unit of composition doesn't map to a process.

Nevertheless, it is not good practice to try and model them with processes than necessary as this can cause TLA to find behaviours that would be impossible in the real system. It also makes behaviour traces quite convoluted.

Cancellation occurs when a stream is started in a different thread and its fiber is cancelled. We can model cancellation by setting the cancellation flag in one process and checking it in the process that does work.

## Cancellation and errors in the observer

The observer pipe is a function, and so could be anything. The following are all valid observer pipes:



```scala
identity
```

```scala
_ => other
```

```scala
in => other.concurrently(in)
```

```scala
_ ++ other
```

The `observer` is the stream that is constructed by the observer pipe. is run in a different fiber using `concurrently`, so may be cancelled.
 - For the identity observer, cancelling the observer is analagous to cancelling the input.
 - The empty observer does not pull on the input whatsoever. Cancelling it has no effect on the input.
   - Nothing is ever sent to the channel
   - The channel is closed once the observer finishes
   - The observer may still do work
 - The concurrent observer is cancelled, and will cancel the input. The input's finalizers are run before the observer's finalizers.
 - The concat observer has work to do after pulling on the in stream. When cancelled it may or may not cancel the observer.
 
There are several cases:
 - The in stream may complete before the observer is cancelled (as in `concat` and `concurrently`)
   `observer = in ++ other`
   => The `in` stream should transition to `done` independently of the observer
 - The `in` stream may never do anything (as in `_ => other`). Mark it as complete 
 - The `in` stream may depend on the observer. We can see this as the observer having no work, or not doing its work.
 
The cases are
 - the `in` stream and `obs` stream are cancelled in the same step
 - the `obs` stream is cancelled first, then the `in` stream, such that the `in` stream may complete before the `obs` stream.
   => The `obs` stream needs to do work independently of the `in` stream. This can be as simple as checking its cancellation flag.
 - at each step in the sinkOut, check if the observer has been cancelled. If it has, then cancel the 

If the observer is NOT synchronous then it may terminate gracefully at some step AFTER the input stream has terminated

# Understanding scopes

The different kinds of input-observer relationships can be summarized by different scoping rules:
 - No related scope, such as in `concurrently`
 - A parent-child relation, such as in `.take`
 - A transient parent-child relation, one that doesn't exist all the time, such as in `++`
 
Additionally, scopes can affect how errors are handled.

`handleErrorWith` creates a parent scope which succeeds when the child scope fails.

```
(Stream(1) ++ Stream.raiseError[IO](new Error())
  .covaryOutput[Int])
  .onFinalizeCase(c => IO.println(s"Finalized 1 with $c"))
  .handleErrorWith(_ => Stream(2, 3))
  .onFinalizeCase(c => IO.println(s"Finalized 2 with $c"))
  .compile.drain
```

So the observer may have a `handleErrorWith`, and thus will succeed even if the input fails.

The input is cancelled then linked parent scope is also cancelled.


Next steps:
 - Write up findings
 - Try a version with ++ for the guard and channel closing.

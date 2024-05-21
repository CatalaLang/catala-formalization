# Lists

When implementing list, there is a design decision to be taken. There is two possible semantics for the evaluation of exceptions.

The first one is to evaluate all exceptions, and then filter them to raise a conflict or not. If one of them raises a fatal error, it is raised at this very moment.

The second one is to evaluate each of the exceptions one by one, filtering them on the way, raising a conflict if two values are computed.

In the absence of side effects (this is our case), both solutions are equivalent and return the same kind of errors when evaluated. But I suspect the proof might be easier when taking the lazy-lists approach.


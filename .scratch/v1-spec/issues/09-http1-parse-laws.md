# Which laws does http1 guarantee for request parsing?

Type: grilling
Status: open
Blocked by: 03, 07, 08, 10
Map: [bend-http v1 spec](../map.md)

## Question

Using the smuggling cases and the request type, decide the exact laws v1 proves: for example, every ambiguous framing case is rejected; parsing never needs more than the limits allow; feeding input in pieces gives the same parse outcome as feeding it at once; the request's path satisfies the urlpath laws; leftover input is exactly what follows the request.

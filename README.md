# bend-http

An HTTP/1.1 request parser for [Bend 2](https://github.com/bendlang/bend), with proofs.

This repo will hold two BendHub packages:

- **`bend-urlpath`** takes the path part of a URL, like `/photos/cat.jpg`, and returns its decoded segments or rejects it with a reason.
- **`bend-http1-server`** reads HTTP/1.1 requests from raw bytes and writes responses back as bytes. It uses `bend-urlpath` for paths.

Neither package opens a socket. Your code reads bytes from the connection, hands them to the parser and sends back the bytes it returns. A small demo server will show how the pieces fit.

## Why write another parser

BendHub already has HTTP code. This project is about laws that hold for every possible input and are checked by Bend's proof checker, rather than tests on a handful of examples. The ones I care most about:

- A request with both `Content-Length` and `Transfer-Encoding` is never parsed. That combination is the classic request smuggling trick.
- Feeding a request in pieces gives the same result as feeding it all at once, so a slow client can't change what the parser sees.
- Every path the parser accepts is free of `..`, encoded slashes and control bytes.

Each law will map to a section of RFC 9112 or to a known smuggling attack. That table goes here once the laws exist.

## Strict on purpose

Where the RFC lets a parser tolerate something odd, this one rejects it. Request smuggling works when a front end and a back end disagree about where a request ends. I'd rather turn away a rare legitimate client than guess.

These are rejected even though the RFC would allow them:

- `Transfer-Encoding: ,chunked`
- a `Content-Length` with leading zeros, or the same `Content-Length` line sent twice
- `HTTP/1.2` through `HTTP/1.9`
- whitespace before `;` in a chunk extension
- `CONNECT`, which isn't implemented and gets a 501

The path parser follows the same rule. It decodes `%XX` exactly once, so `%252F` stays the literal text `%2F`. It refuses `%2F` and `%2e%2e` outright, and it rejects any `..` that would climb above the root.

## How it will work

You call one function on everything received so far on a connection:

```
parse(limits, input) -> Outcome
```

It answers in one of three ways:

- **NeedMore** means the request isn't complete. Read more bytes and call again.
- **Rejected** carries a reason. Send the matching error status and close the connection.
- **Parsed** carries the request plus any leftover bytes. The leftover is the start of the next request on the same connection, so you pass it to `parse` next time.

`limits` caps things like header size and body size, so a client can't make the parser wait forever or hold unlimited memory.

## Layout

```
urlpath/
  urlpath.bend   the code
  LAWS.bend      statements that must hold
  PROOF.bend     one proof per law; the file you check
http1/           same shape, not started yet
```

## Checking the proofs

You need Bend 2 installed at `~/.bend/bin/bend`. From the repo root:

```sh
~/.bend/bin/bend urlpath/PROOF.bend
```

It should print `ALL PROOFS CHECK`. For the full check, add `--verdict`. This rechecks everything with the BendTT kernel, which needs Lean 4.34.0:

```sh
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.0

~/.bend/bin/bend urlpath/PROOF.bend --verdict
```

The first `--verdict` run builds the kernel and takes about 15 seconds. After that a check takes under a second.

## Not in v1

The client side, HTTP/2, TLS, `CONNECT` tunnels and `Upgrade`, and serving files from disk.

## License

MIT

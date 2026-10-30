"""The study's instance reader, shared by every Python solver here.

It is not part of any measurement: readers run before the clock starts, and the
clock covers the solver call alone. It lives here, outside the solver
directories, so that no solver carries a parser of its own.

Format: the DIMACS assignment format of ../assignment_format.pdf, extended with
optional vertex capacities.

    c <comment>
    p asn <nodes> <arcs>        ("p bmatch ..." is accepted as well)
    n <id> [<cap>]              capacity of vertex <id>, default 1
    a <u> <v> [<w>]             edge {u, v}, u on the left, v on the right

Vertex ids run 1..<nodes>. The sides come from the arcs: tails are left, heads
are right. A vertex on both sides is an error, and so is a repeated edge -- the
verified code requires simple graphs. A plain DIMACS assignment file, whose "n"
lines carry no capacity, is read as an ordinary matching instance.
"""


class InstanceError(Exception):
    pass


def read_instance(path):
    """Return (nodes, edges, weights, caps): edges a list of (u, v), caps a dict."""
    nodes = None
    edges, weights = [], []
    caps = {}
    seen = set()
    with open(path) as f:
        for lineno, line in enumerate(f, 1):
            tok = line.split()
            if not tok or tok[0] == 'c':
                continue
            try:
                if tok[0] == 'p':
                    if nodes is not None:
                        raise InstanceError("second problem line")
                    nodes = int(tok[2])
                elif tok[0] == 'n':
                    caps[int(tok[1])] = int(tok[2]) if len(tok) > 2 else 1
                elif tok[0] == 'a':
                    u, v = int(tok[1]), int(tok[2])
                    if (u, v) in seen:
                        raise InstanceError(f"duplicate edge {u} {v}")
                    seen.add((u, v))
                    edges.append((u, v))
                    weights.append(int(tok[3]) if len(tok) > 3 else 1)
                else:
                    raise InstanceError(f"unknown line type {tok[0]!r}")
            except (IndexError, ValueError):
                raise InstanceError(f"line {lineno}: malformed line {line.strip()!r}")
            except InstanceError as e:
                raise InstanceError(f"line {lineno}: {e}")
    if nodes is None:
        raise InstanceError("missing problem line")
    left = {u for u, _ in edges}
    right = {v for _, v in edges}
    if left & right:
        raise InstanceError(f"vertex {min(left & right)} is on both sides")
    for x in left | right | caps.keys():
        if not 1 <= x <= nodes:
            raise InstanceError(f"vertex {x} outside 1..{nodes}")
    for x, c in caps.items():
        if c < 0:
            raise InstanceError(f"negative capacity at vertex {x}")
    return nodes, edges, weights, caps

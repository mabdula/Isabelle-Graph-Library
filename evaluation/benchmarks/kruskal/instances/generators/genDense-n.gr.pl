# PORTABLE COPY FOR THE REPRODUCIBILITY PACKAGE.  As run, $GENPROG and $DIR were
#   $GENPROG = the absolute path of the challenge suite's ch9-1.1/gens/rand/sprand.exe on the benchmark machine;
#   $DIR     = the absolute path of the study's instances/Dense-n directory there
# (absolute paths on the benchmark machine); here they are relative so the script
# runs inside instances/generators after `make' there.  Nothing else differs.
# ============================================================================
#  genDense-n.gr.pl
# ============================================================================
#
#  Dense-n graph family generator.
#
#  The 9th DIMACS Implementation Challenge on shortest paths has no dense
#  family.  All six of its synthetic families -- Square-n, Square-C, Long-n,
#  Long-C, Random4-n, Random4-C -- sit at four arcs per node, and its two road
#  families are sparser still.  So this family is built here, with the
#  challenge's OWN generator and the challenge's own conventions, rather than
#  with anything foreign to the study:
#
#       - num nodes = power of two, 2^10 .. 2^15
#       - num edges = num nodes^2 / 16, so the average degree is n/16 and
#                     grows with the graph: 64 arcs per node at n=1024,
#                     2048 arcs per node at n=32768.  That is dense in the
#                     usual sense, m = Theta(n^2), and it is what separates
#                     this family from every family the challenge shipped.
#       - min edge weight = 0
#       - max edge weight = num nodes      (recorded, but this study is BFS
#                                           and ignores every weight)
#       - node ids in [1..num nodes]
#       - strongly connected, because sprand lays a Hamiltonian cycle on a
#         random permutation of the nodes before it adds anything random
#
#  The ladder stops at 2^15 and not at 2^21 like the sparse families: the
#  arc count squares, so 2^15 already carries 67 million arcs -- about the
#  size of the full USA road network -- and 2^16 would carry 268 million.
#
#  Ten graphs per size, as Square-n and Long-n have, so a table row here is
#  read exactly like a table row there.
#
#  Usage: > perl genDense-n.gr.pl
# ============================================================================

# param setup:

$START   = 10;      # num nodes goes from 2^$START to 2^$END
$END     = 15;      # m = n^2/16, so this is already 67M arcs
$LOWCOST = 0;       # minimum cost of an edge (hi cost = num nodes)
$SEED    = 971;     # seed of pseudo-random generator -- the challenge's own
$TRIALS  = 10;      # number of trials per data point

$GENPROG = "./sprand.exe";
$DIR     = "./Dense-n";
$FORMAT  = "$DIR/Dense-n.%s.%s.gr";


# header:
print "\n* 9th DIMACS Implementation Challenge: Shortest Paths\n";
print   "* http://www.dis.uniroma1.it/~challenge9\n";
print   "* Dense-n family graph generator [degree n/16]\n";


# creates directory (if does not exist)
system "mkdir -p $DIR";


#sets seed
srand ($SEED);


# generation loop:
for ( $p = $START; $p < $END + 1 ; $p++ ) {

    $n = (1<<$p);
    $m = ($n * $n) / 16;
    print "\n>> Generating graph trials for data point [n=2^$p=$n, m=$m]\n";

    # generate trials per data point
    for ( $trial = 0; $trial < $TRIALS; ++$trial) {
        $pathname = sprintf $FORMAT, $p, $trial;
        $trialseed = int(rand(0x7FFFFFFF));
        printf "   - Generating file %s [seed %-10s] ...", $pathname, $trialseed;
        system "$GENPROG $n $m $LOWCOST $n $trialseed > $pathname";
        print " [DONE]\n";
    }
}

# ============================================================================
#  The generator invoked here, sprand, is part of the 9th DIMACS
#  Implementation Challenge distribution and is (C) 2005 Camil Demetrescu and
#  Andrew Goldberg, under the GNU General Public License.  This script follows
#  the shape of the challenge's own genRandom4-n.gr.pl.
# ============================================================================

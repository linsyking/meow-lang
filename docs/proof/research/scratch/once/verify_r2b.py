"""R2b: mirror probes through the same exhaustive MITM machinery.
Targets: del1b (main), delRb = delete the RIGHTMOST b (rev-twin witness),
rep1b = replace leftmost b by a (the paper's second probe).
Depth <= 4 and <= 5, paper vocabulary, full 127-string domain."""
import sys
sys.path.insert(0, '/home/cc/projects/meow-lang/docs/proof/research/scratch/once')
from oncecore import binstrings, const_passes
from search_mitm import mitm

def delRb(C):
    i = C.rfind('b')
    return C if i < 0 else C[:i] + C[i+1:]

def rep1b(C):
    i = C.find('b')
    return C if i < 0 else C[:i] + 'a' + C[i+1:]

if __name__ == '__main__':
    test = binstrings(6)
    passes = const_passes('abc', 2, 2)
    for name, f in (('del1b', lambda C: C[:C.find('b')] + C[C.find('b')+1:] if 'b' in C else C),
                    ('delRb', delRb), ('rep1b', rep1b)):
        tsig = tuple(f(s) for s in test)
        print(f"=== target {name}: depth <= 4", flush=True)
        mitm(test, passes, 2, 2, tsig)
        print(f"=== target {name}: depth <= 5", flush=True)
        mitm(test, passes, 3, 2, tsig)

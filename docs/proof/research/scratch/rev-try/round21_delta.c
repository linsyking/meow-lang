/* round21_delta.c — enumerate ALL real 3-hit drifting-channel
 * configurations on D(k;3) at the necessary-constraint level.
 *
 * Theory (hand-derived, see ROUND21_REPORT.md): a channel (constant c,
 * drift Delta) of a real pass plants at firing sigma at depth
 * Y = BotSum(sigma) + t_sigma*Delta + c, t_sigma = #earlier firings.
 * A HIT is an anchored plant: Y = I(b, a-1) = (3^a - 3^b)/2,
 * 1 <= a <= k+1, 0 <= b < a, (a,b) != (sigma+1, 0) (non-inherited).
 * Three real hits at sigma1 < sigma2 < sigma3 give
 *   W_i := Y_i - BotSum(sigma_i) = (3^{a_i} - 3^{b_i} - 3^{sigma_i+1} + 1)/2
 *        = t_i*Delta + c
 * with 0 <= t1 <= sigma1, q1 := t2-t1 in [1, h1], q2 := t3-t2 in [1, h2]
 * (h_i = sigma spacing: a firing set with these prefix counts exists).
 * So (W1,W2,W3) are COLLINEAR in t with integer slope Delta != 0:
 *   D1 := W2-W1 = q1*Delta,  D2 := W3-W2 = q2*Delta.
 * Necessary (FIT at the hit firings): c <= Delta + 3^{sigma1+1},
 * c >= -3^{sigma1}.  Output-depth monotonicity: I(s1+1,s2)+q1*Delta >= 0,
 * I(s2+1,s3)+q2*Delta >= 0.
 *
 * This prints every configuration passing all of the above — a SUPERSET
 * of the realizable ones.  Build: gcc -O2 -o round21_delta round21_delta.c
 * Run:  ./round21_delta 8 > d8.txt   (k = 8; also 9)
 */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    int k = argc > 1 ? atoi(argv[1]) : 8;
    long long pw[26];
    pw[0] = 1;
    for (int i = 1; i <= k + 2; i++) pw[i] = 3 * pw[i - 1];
    long long nrec = 0, ncol = 0;
    for (int s1 = 0; s1 < k; s1++)
    for (int s2 = s1 + 1; s2 < k; s2++)
    for (int s3 = s2 + 1; s3 < k; s3++) {
        int h1 = s2 - s1, h2 = s3 - s2;
        long long step1 = (pw[s2 + 1] - pw[s1 + 1]) / 2; /* I(s1+1,s2) */
        long long step2 = (pw[s3 + 1] - pw[s2 + 1]) / 2; /* I(s2+1,s3) */
        for (int a1 = 1; a1 <= k + 1; a1++) for (int b1 = 0; b1 < a1; b1++) {
            if (a1 == s1 + 1 && b1 == 0) continue;
            long long W1 = (pw[a1] - pw[b1] - pw[s1 + 1] + 1) / 2;
            for (int a2 = 1; a2 <= k + 1; a2++) for (int b2 = 0; b2 < a2; b2++) {
                if (a2 == s2 + 1 && b2 == 0) continue;
                long long W2 = (pw[a2] - pw[b2] - pw[s2 + 1] + 1) / 2;
                long long D1 = W2 - W1;
                if (D1 == 0) continue;
                for (int a3 = 1; a3 <= k + 1; a3++) for (int b3 = 0; b3 < a3; b3++) {
                    if (a3 == s3 + 1 && b3 == 0) continue;
                    long long W3 = (pw[a3] - pw[b3] - pw[s3 + 1] + 1) / 2;
                    long long D2 = W3 - W2;
                    if (D2 == 0) continue;
                    if ((D1 > 0) != (D2 > 0)) continue;
                    ncol++;
                    long long x = D1 > 0 ? D1 : -D1, y = D2 > 0 ? D2 : -D2;
                    long long g = x, m = y;
                    while (m) { long long t = g % m; g = m; m = t; }
                    long long r1 = x / g, r2 = y / g;
                    for (int n = 1; r1 * (long long)n <= h1 &&
                                    r2 * (long long)n <= h2; n++) {
                        long long q1 = r1 * n, q2 = r2 * n;
                        if (D1 % q1 != 0) continue;
                        long long delta = D1 / q1;
                        if (step1 + q1 * delta < 0) continue;
                        if (step2 + q2 * delta < 0) continue;
                        for (int t1 = 0; t1 <= s1; t1++) {
                            long long c = W1 - (long long)t1 * delta;
                            /* TWO-SIDED tightened FIT (round 21b, the
                             * coordinator's flag): the t1 early firings
                             * occupy distinct positions in [0, s1), so
                             * the FIRST firing tau0 <= s1 - t1, where
                             * BOTH flanks must fit: p1 <= 3^{tau0+1}
                             * and p0 <= 3^{tau0}.  Hence
                             * c <= Delta + 3^{s1-t1+1}  AND
                             * c >= -3^{s1-t1}. */
                            if (c > delta + pw[s1 - t1 + 1]) continue;
                            if (c < -pw[s1 - t1]) continue;
                            nrec++;
                            printf("REC k=%d s=%d,%d,%d ab=%d/%d,%d/%d,%d/%d"
                                   " q=%lld,%lld t1=%d D=%lld c=%lld\n",
                                   k, s1, s2, s3, a1, b1, a2, b2, a3, b3,
                                   q1, q2, t1, delta, c);
                        }
                    }
                }
            }
        }
    }
    fprintf(stderr, "k=%d: collinear-signed candidate triples=%lld"
                    " surviving records=%lld\n", k, ncol, nrec);
    return 0;
}

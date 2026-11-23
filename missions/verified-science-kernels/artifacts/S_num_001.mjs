/**
 * S-num-001: Neumaier-improved Kahan compensated summation.
 * Preserves exact sum even when the next term exceeds the running sum (1e100 cancellation).
 */
export function compensatedSum(xs) {
  let sum = 0.0;
  let c = 0.0;
  for (let i = 0; i < xs.length; i++) {
    const x = xs[i];
    const t = sum + x;
    if (Math.abs(sum) >= Math.abs(x)) {
      c += (sum - t) + x;
    } else {
      c += (x - t) + sum;
    }
    sum = t;
  }
  return sum + c;
}

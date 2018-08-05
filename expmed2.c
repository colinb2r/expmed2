
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define HOST_WIDE_INT int
#define HOST_BITS_PER_WIDE_INT 32
#define HOST_BITS_PER_DOUBLE_INT (2 * HOST_BITS_PER_WIDE_INT)

/* Making GNU GCC choose_multiplier in expmed.c significantly faster.
   By which we mean up to 50% or more faster for the compiler to calculate
   parameters for the machine code for integer division by a constant divisor.
   (Compiled programs won't run faster.)
   Licencing: in Fractint people's words "Don't want money, want recognition!"
   The version choose_multiplier_v2 is based - but improves - on what's in
   the GCC choose_multiplier function in file expmed.c, so the GCC licence.
   The version choose_multiplier_v4 is based - but improves - on magicu2 in
   "Hacker's Delight", so the licence is you needn't acknowledge the source
   but it would be nice to credit the code as from:
   magicu2 in "Hacker's Delight" by Henry S Warren http://hackersdelight.org
   with improvements by Colin Bartlett <colinb2@gmail.com>.

   This is a stand-alone program including:
   * choose_multiplier_v2 intended to replace choose_multiplier in GCC expmed.c;
     using wide_int is slow compared to using fixed width integers,
     so we reduce or eliminate using wide_int;
   * choose_multiplier_v4 which acts as a check on choose_multiplier_v2, and
      improves on magicu2 in Chapter 10 of "Hacker's Delight" by Henry S Warren.
   Key to not obvious output:
   P=precision; L=lgup=ceiling(log2(divisor)); rv=return_value; s=post_shift;
   neq = 0 same, 1 v2_M > v4_M, 2 v2_M < v4_M, 4 rv difference, 8 s difference;
   NEQ = "or" of all neq values, so shows worst cases differences;
   "m>" = count of v2_M > v4_M, with that being the only difference.

   Eric Botcazou has observed (in an email) that reducing or eliminating
   using wide_int might be applicable elsewhere in the GNU GCC compiler.

   Any questions or comments to: colinb2@gmail.com  */

int
ceil_log2 (unsigned long long iv)
{
  /* Returns ceiling(log2(iv)). */
  if (iv == 0) return -1;
  iv -= 1;
  int rv = 0;
  if (iv & 0xFFFFFFFF00000000llu) { iv >>= 32; rv |= 32; }
  if (iv &         0xFFFF0000llu) { iv >>= 16; rv |= 16; }
  if (iv &             0xFF00llu) { iv >>=  8; rv |=  8; }
  if (iv &               0xF0llu) { iv >>=  4; rv |=  4; }
  if (iv &                0xCllu) { iv >>=  2; rv |=  2; }
  return rv + (iv & 0x2llu ? 2 : iv & 0x1llu ? 1 : 0);
}

void
gcc_assert (int iv)
{
  if (iv) return;
  printf ("gcc_assert error\n");
  exit (1);
}



/* Choose a minimal N + 1 bit approximation to 1/D that can be used to
   replace division by D, and put the least significant N bits of the result
   in *MULTIPLIER_PTR and return the most significant bit.

   The width of operations is N (should be <= HOST_BITS_PER_WIDE_INT), the
   needed precision is in PRECISION (should be <= N).

   PRECISION should be as small as possible so this function can choose
   multiplier more freely.

   The rounded-up logarithm of D is placed in *lgup_ptr.  A shift count that
   is to be used for a final right shift is placed in *POST_SHIFT_PTR.

   Using this function, x/D will be equal to (x * m) >> (*POST_SHIFT_PTR),
   where m is the full HOST_BITS_PER_WIDE_INT + 1 bit multiplier.  */


#define CMUHWI1 ((unsigned HOST_WIDE_INT) 1)

/* Why is choose_multiplier "unsigned HOST_WIDE_INT", not just "int"?
   It only returns 0 or 1.                                            */

int
choose_multiplier_v2 (unsigned HOST_WIDE_INT d, int n, int precision,
		   unsigned HOST_WIDE_INT *multiplier_ptr,
		   int *post_shift_ptr, int *lgup_ptr)
{
  int lgup, shiftv, topbit, s;
  unsigned HOST_WIDE_INT mlow, mhigh, mlowv, mhighv;
  unsigned HOST_WIDE_INT remainder_test, half_up_maxint;

  /* Iterate downwards for multiplier and post_shift; there may be "overflows"
     but that's mostly OK as using unsigned integers. This adapts and improves
     the current (2018-07-17) choose_multiplier in GNU GCC expmed.c  */

  /* lgup = ceil(log2(divisor)); */
  lgup = ceil_log2 (d);

  gcc_assert (lgup <= n);

  if (lgup <= 0 || precision < lgup)
    {
      /* It's easier to deal separately with d=1 and PRECISION<lgup;
         if d=1 we need to avoid shifting bits by >= HOST_BITS_PER_WIDE_INT,
         and it's awkward to deal with PRECISION<lgup in the main code.  */
      *multiplier_ptr = d <= 1 ? CMUHWI1 << (n - precision) : 0;
      *post_shift_ptr = 0;
      *lgup_ptr = lgup;
      return d <= 1 ? 1 : 0;
    }

  /* Calculate, if necessary by iterating upwards:
       2^(N-1) <= mlow = floor(2^(N+lgup-1)/d) < 2^N;
       0 <= mlowv = 2^(N+lgup-1) - d * mlow < d;
     there may be "overflows" but that's mostly OK as using unsigned integers.
     Then mlow <= mhigh = floor((2^(N+lgup-1)+2^(N+lgup-1-PRECISION))/d) < 2^n.
     An unlikely case is PRECISION<lgup: we can use mhigh=0, shiftv=0.

     This avoids using wide_int; an alternative using wide_int twice
     is replace the first "else" part below by:
        wide_int val = wi::set_bit_in_zero (shiftv, HOST_BITS_PER_DOUBLE_INT);
        mlow = wi::udiv_trunc (val, d).to_uhwi ();
        mlowv = 0 - d * mlow;

     Currently choose_multiplier initializes at post_shift=lgup. This means
     2^N <= mlow < mhigh < 2^(N+1) and necessitates extensive use of wide_int
     which is relatively slow. By initializing at post_shift=lgup-1 we have
     2^(N-1) <= mlow <= mhigh < 2^N and we can reduce using wide_int to twice;
     or by initializing by if necessary iterating upwards we can completely
     eliminate using wide_int. It may seem weird to iterate upwards and then
     iterate downwards, but emperically average lgup-post_shift-(N-PRECISION)
     is about 1.5, so the post_shift is about lgup-(N-PRECISION)-1.5, and
     initializing at lgup-1 the shift reduction is about N-PRECISION+0.5.
     So this double iteration might be faster than using wide_int twice:
     whether it actually is faster needs benchmarking.  */

  topbit = 0;
  half_up_maxint = CMUHWI1 << (n - 1);
  /* Starting at N+lgup-1 instead of N+lgup works *except* when PRECISION<lgup
     and d=2^(lgup-1)+j, where j>0 is small: sometimes mlow<2^N<=mhigh<2^(N+1).
     A kludge fix is for this case: multiplier = 0, post_shift = 0; return 0.
     A better fix is: shiftv = N + lgup - (PRECISION < lgup ? 2 : 1); but
     that might not work if PRECISION=N-1. So for now use the kludge fix.  */
  shiftv = n + lgup - 1;
  if (shiftv < HOST_BITS_PER_WIDE_INT)
    {
      mlowv = CMUHWI1 << shiftv;
      mlow = mlowv / d;
      mlowv -= d * mlow;
    }
  else
    {
      mlowv = half_up_maxint << 1;
      mlow = (mlowv - d) / d + 1;
      mlowv -= mlow * d;
      remainder_test = (d - 1) >> 1;
      s = n;
      while (s < shiftv)
        {
          s += 1;
          if (mlowv <= remainder_test)
            {
              mlow = mlow << 1;
              mlowv = mlowv << 1;
            }
          else
            {
              mlow = (mlow << 1) | 1;
              mlowv = (mlowv << 1) - d;
            }
        }
    }

  s = shiftv - precision;
  /* Avoid shifts by >= HOST_BITS_PER_WIDE_INT. */
  mhigh = precision < HOST_BITS_PER_WIDE_INT ? mlow >> precision : 0;
  mhighv = (s < HOST_BITS_PER_WIDE_INT ? CMUHWI1 << s : 0) - d * mhigh;
  mhigh += mlow + (mlowv < d - mhighv ? 0 : 1);
  if (mlow < mhigh)
    {
      /* Reduce to lowest terms. */
      shiftv -= n;
      while (shiftv > 0)
        {
          mlowv = mlow >> 1;
          mhighv = mhigh >> 1;
          if (mlowv >= mhighv)
	break;
          mlow = mlowv;
          mhigh = mhighv;
          shiftv -= 1;
        }
    } 
  else
    {
      /* Need to use an extra bit for multiplier. */
      mhigh = ((mhigh - half_up_maxint) << 1) | 1;
      shiftv = lgup;
      topbit = 1;
    }

  *multiplier_ptr = mhigh;
  *post_shift_ptr = shiftv;
  *lgup_ptr = lgup;
  return topbit;
}

int
choose_multiplier_v4 (unsigned HOST_WIDE_INT d, int n, int precision,
		   unsigned HOST_WIDE_INT *multiplier_ptr,
		   int *post_shift_ptr, int *lgup_ptr)
{
  int lgup, shiftv, topbit;
  unsigned HOST_WIDE_INT q, delta, delta_test, half_up_maxint;

  /* Iterate upwards for multiplier and post_shift; there may be "overflows"
     but that's mostly OK as using unsigned integers. This adapts and improves
     magicu2 in Chapter 10 of "Hacker's Delight" by Henry S Warren.  */

  /* lgup = ceil(log2(divisor)); */
  lgup = ceil_log2 (d);

  gcc_assert (lgup <= n);

  if (lgup <= 0 || precision < lgup)
    {
      /* It's easier to deal separately with d=1 and PRECISION<lgup;
         if d=1 we need to avoid shifting bits by >= HOST_BITS_PER_WIDE_INT,
         and it's awkward to deal with PRECISION<lgup in the main code.  */
      *multiplier_ptr = d <= 1 ? CMUHWI1 << (n - precision) : 0;
      *post_shift_ptr = 0;
      *lgup_ptr = lgup;
      return d <= 1 ? 1 : 0;
    }

  topbit = 0;
  half_up_maxint = CMUHWI1 << (n - 1);
  delta_test = d >> 1;
  if (n < HOST_BITS_PER_WIDE_INT)
    {
      delta = CMUHWI1 << n;
      q = delta / d;
    }
  else
    {
      delta = 0;
      q = (0 - d) / d + 1;
    }
  delta = (q + 1) * d - delta;
  shiftv = n - precision;
  /* We want: while (delta > 2^shiftv); but that may overflow. */
  while (shiftv < HOST_BITS_PER_WIDE_INT && ((delta - 1) >> shiftv) != 0)
    {
      shiftv += 1;
      if (delta <= delta_test)
        {
          q = (q << 1) | 1;
          delta = delta << 1;
        }
      else if (q < half_up_maxint)
        {
          q = q << 1;
          delta = (delta << 1) - d;
        }
      else
        {
          /* Need to use an extra bit for multiplier. */
          q = (q - half_up_maxint) << 1;
          topbit = 1;
          break;
        }
    }

  *multiplier_ptr = q + 1;
  *post_shift_ptr = shiftv - (n - precision);
  *lgup_ptr = lgup;
  return topbit;
}

int
test_v2 (int n, int precision, unsigned HOST_WIDE_INT d, int qshow, int *shift_diff)
{
  int s, lgup, lgupv, rv, sv, rvv, neq;
  unsigned HOST_WIDE_INT m, mv;
  rv = choose_multiplier_v2 (d, n, precision, &m, &s, &lgup);
  rvv = choose_multiplier_v4 (d, n, precision, &mv, &sv, &lgupv);
  neq = (m == mv ? 0 : m>mv ? 1 : 2) | (rv == rvv ? 0 : 4) | (s == sv ? 0 : 8);
  *shift_diff = lgup - s - (n - precision);
  if (qshow >= 4 || (neq && qshow))
    printf ("//#// N %2d P %2d L %2d %2d d %10u = 0x%8x; M 0x %8x %8x rv %1d %1d s %2d %2d; neq %2d;\n",
          n, precision, lgup, lgupv, d, d, m, mv, rv, rvv, s, sv, neq);
  return neq;
}

int
range_test_v2 (int n, int precision,
        unsigned HOST_WIDE_INT dfrom, unsigned HOST_WIDE_INT dto, int qdadd)
{
  int shift_diff, neq, neqor = 0;
  unsigned HOST_WIDE_INT dd, sum_shift_diff = 0;
  unsigned HOST_WIDE_INT counteq = 0, countmgt = 0, countneq = 0;
  if (qdadd > 0) dto = dfrom + (dto - 1);
  else if (qdadd < 0)
    {
      dd = dfrom;
      dfrom = dfrom - (dto - 1);
      dto = dd;
    }
  for (dd = dfrom - 1; dd < dto; dd++)
    {
      neq = test_v2 (n, precision, dd + 1, 0, &shift_diff);
      sum_shift_diff += shift_diff;
      neqor |= neq;
      if (neq)
        {
          if (neq == 1 ? countmgt == 0 : countneq < 5)
            test_v2 (n, precision, dd + 1, 1, &shift_diff);
          if (neq == 1) countmgt += 1;
          else countneq += 1;
        }
      else counteq += 1;
    }
  printf ("//#// N %2d P %2d d %u..%u; avg_L-s+P-N %.2f; NEQ %d; eq %u, m> %u, neq %u;\n",
          n, precision, dfrom, dto, (sum_shift_diff * 1.0) / (dto - dfrom + 1),
          neqor, counteq, countmgt, countneq);
  return neqor;
}

void
many_test_v2 (int qshow)
{
  int shift_diff;
  test_v2 (32, 32, 1, qshow, &shift_diff);
  test_v2 (32, 32, 2, qshow, &shift_diff);
  test_v2 (32, 32, 4, qshow, &shift_diff);
  test_v2 (32, 32, 8, qshow, &shift_diff);
  test_v2 (32, 32, 1 << 6, qshow, &shift_diff);
  test_v2 (32, 31, 1 << 6, qshow, &shift_diff);
  test_v2 (32, 26, 1 << 6, qshow, &shift_diff);
  test_v2 (32, 25, 1 << 6, qshow, &shift_diff);
  test_v2 (32, 32, 1 << 31, qshow, &shift_diff);
  test_v2 (32, 32, 3, qshow, &shift_diff);
  test_v2 (32, 32, 5, qshow, &shift_diff);
  test_v2 (32, 32, 6, qshow, &shift_diff);
  test_v2 (32, 32, 7, qshow, &shift_diff);
  test_v2 (32, 31, 7, qshow, &shift_diff);
  test_v2 (32, 30, 7, qshow, &shift_diff);
  test_v2 (32, 29, 7, qshow, &shift_diff);
  test_v2 (32, 28, 7, qshow, &shift_diff);
  test_v2 (32, 32, 9, qshow, &shift_diff);
  test_v2 (32, 32, 10, qshow, &shift_diff);
  test_v2 (32, 32, 11, qshow, &shift_diff);
  test_v2 (32, 32, 12, qshow, &shift_diff);
  test_v2 (32, 32, 25, qshow, &shift_diff);
  test_v2 (32, 32, 125, qshow, &shift_diff);
  test_v2 (32, 32, 625, qshow, &shift_diff);
  test_v2 (32, 32, 102807, qshow, &shift_diff);
  test_v2 (32, 31, 102807, qshow, &shift_diff);
  test_v2 (32, 30, 102807, qshow, &shift_diff);
  return;
}

void
lots_test_v2 ()
{
  int shift_diff, qshow = 1;
  test_v2 (32, 32, 1, qshow, &shift_diff);
  return;
}

int main()
{
  unsigned int umax, u = 5;
  umax = ((1llu << 31) - 1) * 2 + 1;
  many_test_v2 (4);
  range_test_v2 (32, 32, 0*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 1*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 2*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 3*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 4*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 5*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 6*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 7*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 8*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, 9*10*1000*1000 + 1, 10*1000*1000, 1);
  range_test_v2 (32, 32, umax, 10*1000*1000, -1);
  range_test_v2 (32, 32, u, 1000*1000, 1);
  range_test_v2 (32, 31, u, 1000*1000, 1);
  range_test_v2 (32, 30, u, 1000*1000, 1);
  range_test_v2 (32, 29, u, 1000*1000, 1);
  range_test_v2 (32, 28, u, 1000*1000, 1);
  range_test_v2 (32, 20, u, 1000*1000, 1);
  range_test_v2 (32, 19, u, 1000*1000, 1);
  range_test_v2 (32, 18, u, 1000*1000, 1);
  exit (0);
}


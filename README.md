# RootOfMTP
The tool "RootOfMTP" isolates all the real roots of a mixed trigonometric-polynomial (MTP) with Maple 2021.

## Code
All code is in "RootOfMTP.mpl" and "mainIBR.mpl".
- The procedure "RootOfMTP" is used for ``isolating" all the real roots of an MTP.
### Dependency
[Maple 2021](https://www.maplesoft.com.cn/products/maple/professional/index.shtml)
### Using
We illustrate how to use RootOfMTP by a simple example.
Suppose we want to isolate all the real roots of the following MTP by RootOfMTP:
$$x\sin{x} + \cos{x} - 1.$$
We only need to run the following commands in Maple2021:

```maple
read ".../RootOfMTP.mpl";
RootOfMTP(x*sin(x)+cos(x)-1,x,1);
```

Herein, the first command is to read the file, and the inputs of the second command are an MTP, the variable of the MTP and a rational number $\epsilon>0$ which specifies the maximal length of isolating intervals.
The output is

```maple
For every k <= -1 (k in Z), 2kPi+(0) is a real root with multiplicity 1.
For every k >= 1 (k in Z), 2kPi+(0) is a real root with multiplicity 1.
There is 1 real root with multiplicity 2 at 0.
For every k >= 2 (k in Z), there is 1 real root with multiplicity 1 
in (2kPi+(2*arctan(63/16)), 2kPi+(Pi)).
For every k <= -2 (k in Z), there is 1 real root with multiplicity 1 
in (2kPi+(-Pi), 2kPi+(-2*arctan(63/16))).
There is 1 real root with multiplicity 1 in each open interval of the list
[[-5/2*Pi-2*arctan(29666650363354128505/36893488147419103232),
-5/2*Pi-2*arctan(7242537696610193/9007199254740992)],
[-1/2*Pi-2*arctan(7030038563941/17592186044416),
-1/2*Pi-2*arctan(14741934773129570377/36893488147419103232)],
[1/2*Pi+2*arctan(14741934773129570377/36893488147419103232),
1/2*Pi+2*arctan(7030038563941/17592186044416)],
[5/2*Pi+2*arctan(7242537696610193/9007199254740992),
5/2*Pi+2*arctan(29666650363354128505/36893488147419103232)]].
```

## Examples
- Testing examples in "bc_chenMTP.mpl" are from [^1] and [^2].
- Testing examples in "bc_haokun1.mpl" and "bc_haokun2.mpl" are generated randomly.

[^1]:=https://sysmath.com/jweb_xtkxysx/CN/10.12341/jssms12871
[^2]:=https://arxiv.org/abs/2204.01481

## Experimental Results
We present our experimental results in our paper.
All tests were conducted on 16-Core Intel Core i7-12900KF@3.20GHz with 128GB of memory and Windows 11.
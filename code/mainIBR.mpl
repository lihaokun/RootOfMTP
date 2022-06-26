#### @author Tianqi Zhao  Haokun Li



with(RootFinding):


##################### proc mylog2
mylog2 := proc(x)
return log(x)/log(2);
end proc:


###################### proc Numerator
Numerator := proc(fracpoly)
local factorlist, fac, ans;
factorlist := factors(fracpoly);
if  factorlist[1]>0 then
   ans := 1;
else
   ans := -1;
end if;
for fac in factorlist[2] do
    if fac[2]>0 then
       ans := ans * fac[1]^(fac[2]);     # 这里扔掉了常数
    end if;
end do;
return ans;
end proc:

###################### proc WeakFourierSeq (ok)
# The procedure is Algorithm 3 in our paper.
# input:
# poly: a polynomial in Q[x,y]
# var: [x,y]
# output:
# rans: the sequence F_{1}=poly,...,F_{k} in Q[x,y] in Remark 4.10 (not a weak Fourier sequence)
# (ans: the weak Fourier sequence G_{1}^{*}=poly,...,G_{k}^{*} in Q[x,y] in Algorithm 3.)
WeakFourierSeq := proc(poly, var)
option cache;
local ans, i, rans, temp;
i := 1;
ans := [poly];
# print("i", i);
# print("ans[i]", ans[i]);
rans := [poly];
while type(ans[i], constant) = false do
  # print("#########################");
  temp := ArctanDiff(ans[i], var);
  # print("temp", temp);
  ans := [op(ans), temp];
  # print("CommonDeno", CommonDeno(temp));
#   rans := [op(rans), expand(simplify(temp*CommonDeno(temp)))];
  rans := [op(rans), Numerator(temp)];
  # print("rans[i]", rans[i]);
  i := i + 1;
  # print("i", i);
  # print("ans[i]", ans[i]);
end do;
# print("weakseq", ans);
return ans,rans;
end proc:

###################### proc CheckWeakFourierSeq (ok)
CheckWeakFourierSeq := proc(weakseq, var) 
local i, dif, q; 
for i to nops(weakseq) - 1 do 
  # print("########################");
  # print("weakseq[i]", weakseq[i]);
  dif := expand(diff(weakseq[i], var[1])/(var[2]^2 + 1) + diff(weakseq[i], var[2])); 
#   print("dif(weakseq[i])",factor( dif));
#   print("weakseq[i+1]", factor(weakseq[i+1]));
  q := factor(weakseq[i + 1] / dif); 
#--  print("q", q); #--
end do; 
end proc:

###################### proc CheckSeq (ok)
checkseq := proc(rseq, weakseq) 
local i, dif, q; 
for i to nops(rseq) do 
  q := factor(rseq[i]/weakseq[i]); 
#--  print("q", q); #-- 
end do; 
end proc:

###################### proc ArctanDiff (ok)
ArctanDiff := proc(poly, var)
local dif, ans;
# print("degree(poly, var[1])", degree(poly, var[1]));
if degree(poly, var[1])=0 then
   return UnivarPoly(poly, var);
else
  dif := factor(diff(poly, var[1]) / (1 + var[2]^2) + diff(poly, var[2]));
  # dif := diff(poly, var[1]) / (1 + var[2]^2) + diff(poly, var[2]);
  # print("dif", dif);
  # print("CommonDeno(lcoeff(dif, var[1]))", CommonDeno(lcoeff(dif, var[1])));
  ans := expand(factor(dif * CommonDeno(lcoeff(dif, var[1]))));
  # ans := expand(dif * CommonDeno(lcoeff(dif, var[1])));
  return ans;
end if;
end proc:

###################### proc CommonDeno (ok)
# input:
# fracpoly: in Q(x,y)
# output:
# ans: the common denominator of fracpoly
CommonDeno := proc(fracpoly)
local factorlist, fac, ans;
factorlist := factors(fracpoly);
ans := 1;
for fac in factorlist[2] do
    if fac[2]<0 then
       ans := ans * fac[1]^(-fac[2]);
    end if;
end do;
return ans;
end proc:

###################### proc UnivarPoly (ok)
UnivarPoly := proc(poly, var)
local j, deg, dif, lc;
deg := degree(poly, var[2]);
if deg = 0 then
   return 0;
else
   j   := 0;
   # print("j", j);
   dif := diff(poly, var[2]);
   # print("dif", dif);
   lc  := lcoeff(dif);
   # print("lc", lc);
   dif := signum(lc) * dif / lc; 
   # print("dif", dif);
   while coeff(dif, var[2], j)=0 do
     # print("coeff(dif, var[2], j)", coeff(dif, var[2], j));
     j := j + 1;
   end do;
   return expand(dif / var[2]^j);
   # return simplify(dif / var[2]^j);
end if; 
end proc:

###################### proc getconInt
getconInt:=proc(poly,var,c,d,Psign:=1)
   local cc,dd,rootlist,temp,i,ans;
   rootlist := Isolate(poly, [var], 1, output=interval);
   # print("getconInt:",rootlist);
   ans := [];
   cc := c;
   for i from 1 to nops(rootlist) do
      temp := op(2, rootlist[i]);
      if temp[1]>=cc  then 
         dd:=min(temp[1],d);
         if  Psign*subs(var=(cc+dd)/2,poly)>0 then
            ans:=[op(ans),[cc,dd]];
         end if;
      end if; 
      if temp[2]>=d then
         break;
      else
         
         cc:=max(cc,temp[2]);
      end if;
   end do;
   # print("getconInt:",ans);
   return ans;
end proc:

#########proc pairlistminist
pairlistminist:=proc(lst,lstist)
local i,ist,m;
if nops(lst)=0 then
  return 0;
end if;
m:="None";
ist:=0;
for i from 1 to nops(lst) do
  if lstist[i]<=nops(lst[i]) and (m="None" or m>lst[i][lstist[i]][1]) then
    m:=lst[i][lstist[i]][1];
    ist:=i;
  end if;
end do;
return ist;
end proc:
###################### proc getInitInt
getInitInt:=proc(combpoly1, var,ranum,num)
local  cc,dd,temp,wmin, wmax,minint0,maxint0,minint1,maxint1,lst,istlst,i,i1,i2,n,di,ans;
  n  := 6;
  di := ceil(mylog2(max(abs(ranum),1))) + 4;  
  wmin, wmax := BoundPoly(combpoly1, var, n, di,0);
  # print("getInitInt",wmin);
  minint0:=getconInt(wmin,var[2],0,1,1);
  # print("getInitInt",minint0);
  # print("getInitInt",wmax);
  maxint0:=getconInt(wmax,var[2],0,1,-1);
  # print("getInitInt",maxint0);
  wmin, wmax := BoundPoly(combpoly1, var, n, di,1,false);
  # print("getInitInt",wmin);
  minint1:=getconInt(wmin,var[2],0,1,1);
#   print("getInitInt",minint1);
  for i from 1 to nops(minint1) do
   i1,i2:=op(minint1[i]);
   minint1[i]:=[gettanx0totanpi4subx0(i2),gettanx0totanpi4subx0(i1)];
  end do;
#   print("getInitInt",minint1);
  # print("getInitInt",wmax);
  maxint1:=getconInt(wmax,var[2],0,1,-1);
#   print("getInitInt",maxint1);
  for i from 1 to nops(maxint1) do
   i1,i2:=op(maxint1[i]);
   maxint1[i]:=[gettanx0totanpi4subx0(i2),gettanx0totanpi4subx0(i1)];
  end do;
#   print("getInitInt",maxint1);


  lst:=[minint0,maxint0,minint1,maxint1];
  istlst:=[1,1,1,1];
  cc:=0;
  ans:=[];
  i:=pairlistminist(lst,istlst);
  
  while i<>0 do
    temp:=lst[i][istlst[i]];
    istlst[i]:=istlst[i]+1;
    if temp[1]>cc then
      ans:=[op(ans),[cc,temp[1],num]];
    end if;
    if temp[2]>cc then
      cc:= temp[2];
    end if;
    i:=pairlistminist(lst,istlst);
  end do;
  if cc<1 then
    ans:=[op(ans),[cc,1,num]];
  end if;
  return ans;
end proc:


############### getPolyInt
# vmin*vmax
getPolyInt:=proc(poly, var, vmin, vmax,opt:=0)
local wmin, wmax,poly1,vmin1,vmax1,posi, nega;
  if vmin<0 and vmax>0 then
    error "getPolyInt: vmin<0 and vmax>0.";
  end if;
  if vmax<0 then
    poly1:=subs(var[1]=-var[1],poly);
    vmin1:=-vmax;
    vmax1:=-vmin;
  else
    poly1,vmin1,vmax1:=poly,vmin,vmax;
  end if;
  posi, nega := TwoTypeTerm(poly1, var);
#   print("posi",posi);
#   print("nega",nega);
  wmin,wmax:=0,0;
  if (opt<=0) then
    wmin := subs(var[1]=vmin1, posi) + subs(var[1]=vmax1, nega);
  end if;
  if (opt>=0) then
    wmax := subs(var[1]=vmax1, posi) + subs(var[1]=vmin1, nega);
  end if;
  return wmin,wmax;
end proc:

###################### proc SubIBR
# The procedure SubIBR is Algorithm 5 in our paper.
# input: 
# weakseq: a sequence in Remark 4.10, where weakseq[1] is an irreducible factor in Q[x,y]
# var: [x,y]
# ranum: k, k+\frac{1}{4} 
# output: 
# ans: the set of isolating cubes of real roots of weakseq[1](x,\tan{x}) in (ranum\pi, ranum\pi+\frac{\pi}{4})
SubIBR := proc(weakseq, var, ranum, nstart:=3, nstep:=3, eps:=1)
local ss, lindex, lnum, k, sgc, ans, c, d, m, num, u, v, tweakseq,tweakseq1,tweakseq2, i, j, temp, tempseq, st, sgcleft, sgcright;
k        := nops(weakseq);
# tweakseq := [seq(expand(subs(var[1]=ranum*Pi+arctan(var[2]), weakseq[i])), i=1..k)];
# 
tweakseq1:=expand(subs(var[1]=ranum*Pi+arctan(var[2]), weakseq[1]));
#--print("SubIBR:", ranum);#--
# print("var",var);
ans    := [];
ss     := getInitInt(tweakseq1,var,ranum,k);
lindex := 1;
lnum   := nops(ss);
#--print("ss:",ss,lnum);#--
while lindex<=lnum do
#--  print("******************************");#--
  temp := ss[lindex];
#   print("temp", temp);
  lindex := lindex+1;
  c := temp[1];
  d := temp[2];
  m := temp[3];
#--  print("c,d:",c,d);#--
#   DetectConstPosi(weakseq[1], c, d, ranum, var);
   # if DetectConstPosi(weakseq[1], c, d, ranum, var)<>0 then 
      #   sgc:=0;
   # else
#--      st := time[real]():#--
      #  sgcleft, sgcright := SGC(c, d, var, weakseq, ranum, m);
      #  #   print("sgcleft", sgcleft);
      #  #   print("sgcright", sgcright);
      #  sgc := sgcleft[1] - sgcright[1];
      #   print("the main sgc", sgc);
      sgc,num:=newSGC(c, d, var, weakseq, ranum, m);
#--       print("the main sgc", sgc,num);#--
#--      print("time of main SGC:",sgc,num, time[real]() - st);#--
#   end if;
  if sgc=1 then
#--      print("find",c,d);#--
      while evalf(arctan(d)-arctan(c)-eps)>=0 do
         c,d := Refine(tweakseq1, var, c, d);      
      end do;
#--      print("add",c,d);#--
      ans := [op(ans), [ranum*Pi+arctan(c), ranum*Pi+arctan(d)]];
  elif sgc>=2 then
      # st := time[real]():
      # for i from 2 to m do       
      #    if sgcleft[i]-sgcright[i]=1 then 
      #       num := i; 
      #       break; 
      #    end if;
      # end do;
      # num:=sgc;
      # print("num", num);
      # print("time of finding l:", time[real]() - st);
      if divide(weakseq[num], weakseq[1],'q') then
         error "FAIL: In the weak Fourier sequence, G_{1} divides G_{num}.";  
      else
        #  print("c,d", c,d);
        #  print("G1:", weakseq[1]);
        #  print("G2:", weakseq[num]);
        #  print("w2:", tweakseq[num]);
#--         st := time[real]():#--
         # u,v := RationalEndpoint(tweakseq[1], tweakseq[num], var, c, d, nstart, nstep, distart, distep);
#--         print("num:",num);#--
         tweakseq2:=expand(subs(var[1]=ranum*Pi+arctan(var[2]), weakseq[num]));
         u,v := IntervalEndpoint(weakseq[1], weakseq[num], tweakseq1, tweakseq2, var, ranum, c, d, nstart, nstep);
#--         print("u,v:",u,v);#--
#--         print("one time of RationalEndpoint:", time[real]() - st);#--
         if u>c then
            lnum := lnum + 1;
            ss := [op(ss), [c,u,num]];
         end if;
         if v<d then
            lnum := lnum + 1;
            ss := [op(ss), [v,d,num]];
         end if;
      end if;
  end if; 
end do;
# print("lindex:", lindex);
return ans;
end proc:


###################### proc mtpsignum
mtpsignum :=proc(mtp,var,ranum,d)
local tmp,tx,fx,px,poi,xmax,xmin,di,n,wmin,wmax;
tx:=ranum*Pi+arctan(d);
px:=expand(subs(var[2]=d,mtp));
if px=0 then
   return 0;
else

  #  print(px);
  n  := 3;
  di := ceil(mylog2(max(abs(ranum),1))) + 4;
  xmin, xmax := ForX(ranum, d, d, n, di);
  wmin,wmax :=getPolyInt(px,var,xmin,xmax);
  if wmin>0 then 
    return 1;
  elif wmax<0 then
    return -1;
  else
    return signum(subs(var[1]=tx,px));
  end if;
  # tmp:=evalf(subs(var[1]=evalf(tx),px));
  # poi:=1e-3;
  # if tmp>poi then
  #   return 1;
  # elif  tmp<-poi then
  #   return -1;
  # else
  #   return signum(subs(var[1]=tx,px));
  # end if
end if;
end proc:
###################### proc SGC
# input:
# c, d: two rational numbers
# var: [x, y]
# polyseq: [G_1,...,G_k], where G_{j} in \Q[x,y]
# tweakseq: [w_1:=G_1(ranum*\pi+\arctan{y},y),...,w_k:=G_k(ranum*\pi+\arctan{y},y)]
# m: m<=k
# output:
# sgcleft: [sgc_{1,m}(c^{+}),...,sgc_{m-1,m}(c^{+})]
# sgcright: [sgc_{1,m}(d^{-}),...,sgc_{m-1,m}(d^{-})]
SGC := proc(c, d, var, polyseq, ranum, m)
local signlistl, signlistr, sgcleft, sgcright,st;
#--st:=time[real]();#--
signlistl, signlistr := SignList(c, d, var, polyseq, ranum, m);
#--print("SignList:",time[real]()-st);#--
#--st:=time[real]();#--
sgcleft, sgcright := SgcList(signlistl, signlistr, m);
#--print("SgcList:",time[real]()-st);#--

return sgcleft, sgcright;
end proc:

###################### proc newSGC
newSGC := proc(c, d, var, polyseq, ranum, m)
local st,ist,sc,sd,sc1,sd1,sgc,num;
#--st:=time[real]();#--
ist:=m-1;
sc1:=mtpsignum(polyseq[m],var,ranum,(c+d)/2);
sd1:=sc1;
if sc1=0 then
   error "newSGC FAIL: w_m=0.";  
end if;
num:=0;sgc:=0;
while ist>0 do
  sc:=mtpsignum(polyseq[ist], var,ranum, c);
  sd:=mtpsignum(polyseq[ist], var,ranum, d);
  if sc=0 then
    if sc1>0 then sc := 1; 
    else sc:=-1;
    end if;
  end if;
  if sd=0 then
    if sd1>0 then sd := 1; 
    else sd:=-1;
    end if;
  end if;
  if sd<>sd1 then 
    sgc:=sgc-1;
  end if;
  if sc<>sc1 then
    sgc:=sgc+1;
  end if;
  if sgc=1 then
    num:=ist;
  end if;
  ist:=ist-1;
  sc1,sd1:=sc,sd;
end do;
#--print("newSGC:",time[real]()-st);#--
if sgc<0 then
   error "FAIL: newSGC:sgc<0."; 
end if;
return sgc,num;
end proc:


###################### proc SignList (ok)
# input:
# c, d: two rational numbers
# var: [x, y]
# polyseq: [G_1,...,G_k], where G_{j} in \Q[x,y]
# tweakseq: [w_1:=G_1(ranum*\pi+\arctan{y},y),...,w_k:=G_k(ranum*\pi+\arctan{y},y)]
# m: m<=k
# output:
# signlistl: [sign(w_1,c^{+}),...,sign(w_m,c^{+})]
# signlistr: [sign(w_1,d^{-}),...,sign(w_m,d^{-})]
# SignList := proc(c, d, var, polyseq, tweakseq, m)
SignList := proc(c, d, var, polyseq, ranum, m)
local signlistl, signlistr, prelistl, prelistr, templ, tempr, i, j, st, s, forx, temp;
s := mtpsignum(polyseq[m],var,ranum,(c+d)/2);
# print("s",s);
if s<>0 then
   signlistl := [s];
   signlistr := signlistl;
else
   error "FAIL: sign(w_m((c+d)/2))=0.";  
end if;
#--st:=time[real]():#--
# forx := EvalfForX(ranum, c);
# prelistl  := [seq(SignLimitPair(polyseq[i], ranum, var, c, forx), i=1..m-1), s];
# forx := EvalfForX(ranum, d);
# prelistr  := [seq(SignLimitPair(polyseq[i], ranum, var, d, forx), i=1..m-1), s];
prelistl  := [seq(mtpsignum(polyseq[i], var,ranum, c), i=1..m-1), s];
prelistr  := [seq(mtpsignum(polyseq[i], var,ranum, d), i=1..m-1), s];
# prelistl  := [seq(SignLimit(polyseq[i], tweakseq[i], var, c), i=1..m-1), s];
# prelistr  := [seq(SignLimit(polyseq[i], tweakseq[i], var, d), i=1..m-1), s];
# print("prelistl", prelistl);
# print("prelistr", prelistr);
# print("time of SignList prelistl, prelistr", time[real]()-st);
for j from m-1 by -1 to 1 do
   templ := prelistl[j];
   tempr := prelistr[j];
   if templ<>0 then
      signlistl := [templ, op(signlistl)];
   end if;
   if tempr<>0 then
      signlistr := [tempr, op(signlistr)];
   end if;
   if templ=0 then
      if signlistl[1]>0 then signlistl := [1, op(signlistl)]; 
      else signlistl := [-1, op(signlistl)];
      end if;
   end if;
   if tempr=0 then
      if signlistr[1]>0 then signlistr := [-1, op(signlistr)]; 
      else signlistr := [1, op(signlistr)];
      end if;
   end if; 
end do;
# print("time of SignList final", time[real]()-st);
return signlistl, signlistr;
end proc:

###################### proc EvalfForX
EvalfForX := proc(ranum, q)
return evalf(ranum*Pi+arctan(evalf(q)));
end proc:

###################### proc SgcList (ok)
# input:
# signlistl
# signlistr
# m: nops(signlistl)
# output:
# sgcleft: [sgc_{1,m}(c^{+}),...,sgc_{m-1,m}(c^{+})]
# sgcright: [sgc_{1,m}(d^{-}),...,sgc_{m-1,m}(d^{-})]
SgcList := proc(signlistl, signlistr, m)
local sgcleft, sgcright, j, templ, tempr, st;
#--st := time[real]():#--
if signlistl[m-1]*signlistl[m]>0 then
   sgcleft:=[0];
elif signlistl[m-1]*signlistl[m]<0 then
   sgcleft:=[1];
end if;
if signlistr[m-1]*signlistr[m]>0 then
   sgcright:=[0];
elif signlistr[m-1]*signlistr[m]<0 then
   sgcright:=[1];
end if;
# print("Pre time of sgc:",time[real]()-st);
for j from m-2 by -1 to 1 do
   templ := sgcleft[1];
   tempr := sgcright[1];
   if signlistl[j]*signlistl[j+1]>0 then
      sgcleft := [templ, op(sgcleft)];
   elif signlistl[j]*signlistl[j+1]<0 then
      sgcleft := [templ+1, op(sgcleft)];
   end if;
   if signlistr[j]*signlistr[j+1]>0 then
      sgcright := [tempr, op(sgcright)];
   elif signlistr[j]*signlistr[j+1]<0 then
      sgcright := [tempr+1, op(sgcright)];
   end if;
   # print("One time of sgc:",time[real]()-st);
end do;
return sgcleft, sgcright;
end proc:

###################### proc SignLimit (ok)
# input:
# combpoly: poly(ranum*\pi+\arctan{y},y), where poly in \Q[x,y]
# var: [x,y]
# c: a rational number
# output:
# ans: the sign of compoly at c (also at c^{+}, c^{-})
#      (if compoly(c)=0, then ans=0) 
SignLimit := proc(poly, combpoly, var, c)
local vvalue, st;
# st:=time[real]():
if subs(var[2]=c, poly)=0 then   
   # print("one time of SignLimit subs:",time[real]()-st); 
   return 0;
else 
   vvalue := subs(var[2]=c, combpoly);
   # print("one time of SignLimit signum:",time[real]()-st);
   return signum(vvalue); 
   #######!!!!!! signum uses float numbers to compute
   ####### note that signum(0)=0
end if;
end proc:

###################### proc SignLimitPair (ok)
# input:
# combpoly: poly(ranum*\pi+\arctan{y},y), where poly in \Q[x,y]
# var: [x,y]
# c: a rational number
# output:
# ans: the sign of compoly at c (also at c^{+}, c^{-})
#      (if compoly(c)=0, then ans=0) 
SignLimitPair := proc(poly, ranum, var, c, forx)
local vvalue, st, temp;
# st:=time[real]():
temp := subs(var[2]=c, poly);
if temp=0 then   
   # print("one time of SignLimit subs:",time[real]()-st); 
   return 0;
else 
   vvalue := subs(var[1]=forx, temp);
   # print("one time of SignLimit signum:",time[real]()-st);
   return signum(vvalue); 
   #######!!!!!! signum uses float numbers to compute
   ####### note that signum(0)=0
end if;
end proc:


###################### proc SignLimitNew (ok)
# input:
# combpoly: poly(ranum*\pi+\arctan{y},y), where poly in \Q[x,y]
# var: [x,y]
# c: a rational number
# output:
# ans: the sign of compoly at c (also at c^{+}, c^{-})
#      (if compoly(c)=0, then ans=0) 
SignLimitNew := proc(poly, ranum, var, c)  # 输入把combpoly改成ranum
local temp, di, distep, n, nstep, posi, nega, xmin, xmax, wmax, wmin;
# 加一步c=0, raum=0
# v := subs(var[1]=ranum*Pi+arctan(var[2]), poly);
if c=0 and ranum=0 then
    return sign(subs(var[1]=0,var[2]=0,poly));
end if;
temp := subs(var[2]=c, poly);
if temp=0 then    
   return 0;
else 
      di := 0;
      distep := 3;
      n :=  0;
      nstep := 3;
      # posi, nega := TwoTypeTerm(temp,[var[1]]);
   while true do 
      di := di+distep;
      n := n+nstep;
      xmin, xmax := ForX(ranum, c, c, n, di);
      wmin,wmax := getPolyInt(temp,[var[1]],xmin,xmax);
      # wmin := subs(var[1]=xmin, posi) + subs(var[1]=xmax, nega);
      # wmax := subs(var[1]=xmax, posi) + subs(var[1]=xmin, nega);
      if wmin<0 and wmax<0 then
         return -1;
      end if;
      if wmin>0 and wmax>0 then
         return 1;
      end if;     
   end do;
      # until false;
   # vvalue := subs(var[2]=c, combpoly);   
   # return signum(vvalue);
   # #######!!!!!! signum uses float numbers to compute
end if;
end proc:

###################### proc SGCNum (ok)
# input:
# signlist: a list whose elements are 1 and -1
# output:
# ans: if the number of sign changes in signlist is 0, ans=0; 
#      if the number of sign changes in signlist >= 1, ans=1
SGCNum := proc(signlist)
local ans, i;
ans := 0;
for i from 1 to nops(signlist)-1 do
   # if ans>=2 then break; end if;
   if signlist[i]*signlist[i+1]<0 then
      ans := ans + 1; break;
   end if; 
end do;
return ans;
end proc:

###################### proc SGCNUM (ok)
# input:
# signlist: a list whose elements are 1 and -1
# output:
# ans: the number of sign changes in signlist 
SGCNUM := proc(signlist)
local ans, i;
ans := 0;
for i from 1 to nops(signlist)-1 do
   # if ans>=2 then break; end if;
   if signlist[i]*signlist[i+1]<0 then
      ans := ans + 1; 
   end if; 
end do;
return ans;
end proc:

###################### proc RationalEndpoint
# input:
# combpoly1
# combpoly2
# var: [x,y]
# c,d: two rational numbers such that compoly2 has exactly one simple root sr in (c,d)
# output:
# u,v: two rational numbers such that c<u<sr<v<d and combpoly1 has no roots on [u,v]
# RationalEndpoint := proc(combpoly1, combpoly2, var, c, d, nstart:=1, nstep:=1, distart:=3, distep:=1)
# local cc, dd, n, di, wmin, wmax, q, stseqmax, stseqmin, maxnum, minnum, left, mid, maxend, minend, t, submax, submin, times;
# cc := c;
# dd := d;
# while dd-cc>0.01 do
#    cc, dd := Refine(combpoly2, var, cc, dd);
# end do;
# n := nstart;
# di := distart;
# wmin, wmax := BoundPoly(combpoly1, var, n, di);
# # print("lower:", wmin);
# # print("upper:", wmax);
# t := 0;
# while n>=nstart do
#    # print("################");
#    # print("cc,dd", cc, dd);
#    q := (cc+dd)/2;
#    maxend := 0;
#    minend := 0;
#    if subs(var[2]=cc, wmax)=0 or subs(var[2]=dd, wmax)=0 then
#       maxend := 1;
#    end if;
#    if subs(var[2]=cc, wmin)=0 or subs(var[2]=dd, wmin)=0 then
#       minend := 1;
#    end if;
#    minnum := TranBound(wmin, [var[2]], cc, dd);
#    maxnum := TranBound(wmax, [var[2]], cc, dd); 
#    submax := subs(var[2]=q,wmax);
#    submin := subs(var[2]=q,wmin);
#    # print("minnum, maxnum", minnum, maxnum);
#    # print("submin, submax", sign(submin), sign(submax));
#    if maxend=0 and maxnum=0 and submax<0 then
#       return cc,dd;
#    elif minend=0 and minnum=0 and submin>0 then
#       return cc,dd;
#    elif (maxend+maxnum+minend+minnum=0 and submax>0 and submin<0) or t>5 then
#       n := n + nstep; 
#       di := di + distep;
#       wmin, wmax := BoundPoly(combpoly1, var, n, di);
#       # print("do one time proc BoundPoly");
#       # print("lower:", wmin);
#       # print("upper:", wmax);
#       t:=0;
#    else
#       t := t+1;
#       times := 0;
#       for times from 1 to 7 do
#          cc, dd := Refine(combpoly2, var, cc, dd);
#       end do;
#    end if;
# end do;
# end proc:

###################### proc IntervalEndpoint
# input:
# poly1, poly2, combpoly2
# var: [x,y]
# c,d: two rational numbers such that compoly2 has exactly one simple root sr in (c,d)
# output:
# u,v: two rational numbers such that c<u<sr<v<d and combpoly1 has no roots on [u,v]
IntervalEndpoint := proc(poly1, poly2, combpoly1, combpoly2, var, ranum, c, d, nstart:=3, nstep:=3)
local cc, dd,cc1,dd1,cc2,dd2, mid,n, di, distep, posi, nega, xmin, xmax, wmin, wmax, t, times, q, maxend, minend,
 maxnum, minnum, submax, submin, mixtime,mixtimec;
mixtime := 15;
# mixtimec:=2;
cc := c;
dd := d;
while dd-cc>0.01 do   
   cc, dd := Refine(combpoly2, var, cc, dd);
end do;
n  := nstart;
di := ceil(mylog2(max(abs(ranum),1))) + 4;
# print("di", di);
distep := max(ceil(di/2), 3);
# print("distep", distep);
# posi, nega := TwoTypeTerm(poly1, var);
if n>mixtime then
#--    print("n di",n,di);#--
    xmin, xmax := ForX(ranum, cc, dd, n, di);
    # print("xmin:", xmin);
    # print("xmax:", xmax);
    wmin,wmax:=getPolyInt(poly1,var,xmin,xmax);
    # wmin := subs(var[1]=xmin, posi) + subs(var[1]=xmax, nega);
    # wmax := subs(var[1]=xmax, posi) + subs(var[1]=xmin, nega);
else 
#--    print("IntervalEndpoint",n,di,cc);#--
    wmin, wmax := BoundPoly(combpoly1, var, n, di,cc);
end if;
# print("combpoly1:", combpoly1);
# print("wmin:", wmin);
# print("wmax:", wmax);
t := 0;
while n>=nstart do
   # print("##");
#--   print("cc,dd", cc, dd);#--
   q := (cc+dd)/2;
   maxend := 0;
   minend := 0;
  #  if subs(var[2]=cc, wmax)=0 or subs(var[2]=dd, wmax)=0 then
  #     maxend := 1;
  #  end if;
  #  if subs(var[2]=cc, wmin)=0 or subs(var[2]=dd, wmin)=0 then
  #     minend := 1;
  #  end if;
  #  print("maxend, minend:", maxend, minend);
   # if di<20 then
   #     print("wmin",wmin);
   #     print("wmax",wmax);
   # end if;
   # minnum := TranBound(wmin, [var[2]], cc, dd);
   # maxnum := TranBound(wmax, [var[2]], cc, dd);
   submax := subs(var[2]=q,wmax);
   submin := subs(var[2]=q,wmin);   
#--   print("submin, submax", evalf(submin),evalf(submax));#--
    # if submin<0 and submax>0 then
    # minnum,maxnum:=1,1;
    # else
    minnum,cc1,dd1 := TranBoundRF2(wmin, [var[2]], cc, dd,c,d);
    maxnum,cc2,dd2 := TranBoundRF2(wmax, [var[2]], cc, dd,c,d); 
#--    print("minnum, maxnum", minnum, maxnum);#--
    # end if; 
    # print("submin, submax", sign(submin), sign(submax));
    if maxend=0 and maxnum=0 and submax<0 then
      return cc,dd;
    elif minend=0 and minnum=0 and submin>0 then
      return cc,dd;
    elif (maxend+maxnum+minend+minnum=0 and submax>0 and submin<0) or t>5 then
    # else
      n := n + nstep; 
      di := di + distep;
      # cc, dd := Refine(combpoly2, var, cc, dd);
      for times from 1 to 7 do
      cc, dd := Refine(combpoly2, var, cc, dd);
      end do;
      if n>mixtime then
#--        print("n di",n,di);#--
        xmin, xmax := ForX(ranum, cc, dd, n, di);
        # print("xmin:", xmin);
        # print("xmax:", xmax);
        wmin,wmax:=getPolyInt(poly1,var,xmin,xmax);
        # wmin := subs(var[1]=xmin, posi) + subs(var[1]=xmax, nega);
        # wmax := subs(var[1]=xmax, posi) + subs(var[1]=xmin, nega);
      else
#--        print("IntervalEndpoint",n,di,cc);#--
        wmin, wmax := BoundPoly(combpoly1, var, n, di,cc);
      end if;
      # print("do one time proc BoundPoly");
      # print("lower:", wmin);
      # print("upper:", wmax);
      t := 0;
    else
      t := t+1;
      for times from 1 to 7 do
      cc, dd := Refine(combpoly2, var, cc, dd);
      end do;
    end if;
end do;
end proc:




############## DetectConstPosi
DetectConstPosi := proc(poly1, cc, dd, ranum, var)
local n, di, posi, nega, xmin, xmax, wmin, wmax, minnum, maxnum, submax, submin, q, combpoly1,cc1,dd1;
n  := 3;
di := ceil(mylog2(max(abs(ranum),1))) + 4;
#--print("di", di);#--
# print("distep", distep);
q:=(cc+dd)/2;
combpoly1 := expand(subs(var[1]=ranum*Pi+arctan(var[2]), poly1));
# print("combpoly1",combpoly1);
#--print("DetectConstPosi",n,di,cc);#--
if cc<0 then
  wmin, wmax := BoundPoly(combpoly1, var, n, di,cc);
else
  xmin, xmax := ForX(ranum, cc, dd, n, di);
  wmin,wmax :=getPolyInt(poly1,var,xmin,xmax);
  # posi, nega := TwoTypeTerm(poly1, var);
  # print("posi",posi);
  # print("nega",nega);
  # xmin, xmax := ForX(ranum, var, cc, dd, n, di);
#   print("xmin:", xmin);
#   print("xmax:", xmax);
  # wmin := subs(var[1]=xmin, posi) + subs(var[1]=xmax, nega);
  # wmax := subs(var[1]=xmax, posi) + subs(var[1]=xmin, nega);
end if;
# posi, nega := TwoTypeTerm(poly1, var);
# xmin, xmax := ForX(ranum, var, cc, dd, n, di);
# if cc=538604860581728662879/18889465931478580854784 then
#    printf("wmin: %a\n", wmin);
#    printf("wmax: %a\n", wmax);
# end if;
#--print("DetectConstPosi BoundPoly done.");#--
# wmin := subs(var[1]=xmin, posi) + subs(var[1]=xmax, nega);
# wmax := subs(var[1]=xmax, posi) + subs(var[1]=xmin, nega);
minnum,cc1,dd1 := TranBoundRF2(wmin, [var[2]], cc, dd,cc,dd);
maxnum,cc1,dd1 := TranBoundRF2(wmax, [var[2]], cc, dd,cc,dd); 
print("minnum:", minnum,maxnum);
# minnum := TranBound(wmin, [var[2]], cc, dd);
# maxnum := TranBound(wmax, [var[2]], cc, dd); 
submax := subs(var[2]=q,wmax);
submin := subs(var[2]=q,wmin);
# print("submin:", submin);
#--print("DetectConstPosi done.");#--
if minnum=0 and submin>0 then
   return 1;
elif maxnum=0 and submax<0 then
   return -1;
else
   return 0;
end if;
end proc:


############## proc ArctanInt
# input:
# n: about Taylor series
# c: a rational number, 0<c<1
# output:
# taylormin, taylormax: a low bound and an upper bound in Q[Pi] for arctan(c), maybe contain Pi
#return min,max
# arctan(c)
# d=tan(pi/4-arctan(c))
# arctan(d)=pi/4-arctan(c)
# arctan(c)=pi/4-arctan(d)=pi/4-arctan((1-c)/(1+c))
ArctanInt :=proc(n, c)
local taylormax,c0, taylormin,x,x1,i,len,st,var;
# st:=time[real]();

if  (c<6/10) then 
   taylormax:=  subs(var= c,MTM:-taylor(arctan(var), 4*n+2));
   taylormin:=  taylormax-c^(4*n+1)/(4*n+1);
else   # 计算 Pi/4 - Integral_{c}^{1} 1/(x^2+1) dx
  #  len:=30*n;   # 把 (c,1) 区间分成 len 段
  #  x:=1;    # 从区间 (1-(1-c)/len, 1) 开始, x 记录该区间的右端点, x1 记录该区间的左端点
  #  taylormax:=Pi/4;
  #  taylormin:=Pi/4;
  #  for i from 1 to len do    
  #     x1:=x-(1-c)/len;
  #     taylormax:=taylormax-(1-c)/len/(1+x^2);
  #     taylormin:=taylormin-(1-c)/len/(1+x1^2);
  #     x:=x1;
  #  end do;
  c0:=(1-c)/(1+c);
  taylormax:=  subs(var=c0,MTM:-taylor(arctan(var), 4*n+2));
  taylormin:=  taylormax-c0^(4*n+1)/(4*n+1);
  taylormin,taylormax:=Pi/4-taylormax,Pi/4-taylormin;

end if;
# print(x);
# print(" taylormin,taylormax:",evalf(taylormin),evalf(taylormax));
# print("t:",time[real]()-st);
# st:=time[real]();
# len:=8*n;
# if (c<1/2) then
#    taylormax:=  subs(var= c,MTM:-taylor(arctan(var), len+2));
#    taylormin:=  subs(var= c,MTM:-taylor(arctan(var), len));
# else
#    taylormax:=  subs(var= c,MTM:-taylor(arctan(var), len+2,1));
#    taylormin:=  subs(var= c,MTM:-taylor(arctan(var), len,1));
# end if;
# print(" taylormin,taylormax:",taylormin,taylormax);
# print("t:",time[real]()-st);
return taylormin,taylormax;
end proc:


############## proc ArctanPolyInt
# return  taylormin, taylormax;
ArctanPolyInt := proc(var,  n)
local taylormax, taylormin,taylormax0,taylormin0;

taylormax := MTM:-taylor(arctan(var), 4*n+2);
taylormin :=taylormax-var^(4*n+1)/(4*n+1);

return taylormin, taylormax;
end proc:
############## proc ForX
# input:
# ranum: k or k + 1/4, where k in Z
# var: [x, t], where x will be replaced with ranum*Pi + arctan(t)
# c1, d1: two rational numbers
# n: for Taylor series
# di: for Pi
# output:
# ansmin, ansmax: a lower bound and an upper bound in Q for ranum*Pi + arctan(t), where t in (c1, d1)
ForX := proc(ranum, c1, d1, n, di)
local ansmin, ansmax, taylormax, taylormin, taylormax0, taylormin0,pimin, pimax;
pimin, pimax :=  ForPi(di);
# taylormax0:=  subs(var[2]= c1,MTM:-taylor(arctan(var[2]), 4*n+2));
# taylormin0:=  subs(var[2]= c1,MTM:-taylor(arctan(var[2]), 4*n));
# taylormin,taylormax := ArctanPolyInt(var[2],n,c1);
# print("forx:",pimin,pimax);
if c1=d1 then
  taylormin, taylormax := ArctanInt(n,c1);
else
  taylormin, taylormax0 := ArctanInt(n,c1);   # arctan(c1) 的下界和上界, 可能含 Pi
  taylormin0, taylormax := ArctanInt(n,d1);   # arctan(d1) 的下界和上界, 可能含 Pi
end if;
# print("forx:",taylormin,taylormax);
taylormin, taylormax := EstimatePi(taylormin, taylormax, [Pi, var[2]], di);
# print("forx:",taylormin,taylormax);
# taylormax := MTM:-taylor(arctan(var[2]), 4*n+2,c1)-arctan(c1)+evalf(arctan(c1));
# taylormin := MTM:-taylor(arctan(var[2]), 4*n, c1)-arctan(c1)+evalf(arctan(c1));
if ranum>=0 then
  ansmin  := ranum * pimin + taylormin;
  ansmax  := ranum * pimax + taylormax;
else
  ansmin  := ranum * pimax +taylormin;
  ansmax  := ranum * pimin +taylormax;
  if ansmax>0 then
   ansmax:=0;  
  end if;
end if;
return ansmin, ansmax;
end proc:

############## proc Refine
# input:
# combpoly2: w_{num}(ranum*Pi+arctan(t))
# var: [x,t]
# c1, d1: two rational numbers such that combpoly2 has exact one simple root in (c1, d1)
# output
# cc, dd: (cc, dd) subseteq (c1, d1), dd-cc <= (d1-c1)/2 and combpoly2 has exact one simple root in (cc, dd)
Refine := proc(combpoly2, var, c1, d1)
local left, mid, cc, dd, q;
cc := c1; dd := d1;
q := (cc+dd)/2;
left := signum(subs(var[2]=cc, combpoly2));   # 使用浮点指令 signum
mid  := signum(subs(var[2]=q, combpoly2));    # 使用浮点指令 signum
if mid=0 then   # 先不改，提升arctan和Pi精度，使得wmax和wmin在mid处同号，对wmax和wmin做实根隔离取一个含mid的区间
   cc := (63*q + cc)/64; dd := (63*q + dd)/64;  
elif left * mid = -1 then
   dd := q;    
else
   cc := q;     
end if;
return cc,dd;
end proc:

###################### proc TranBound
# input
# boundpoly: a polynomial in Q[y]
# var: [y]
# c, d: two rational numbers
# output:
# sgc: if sgc=0, boundpoly has no roots in (c,d)
#      if sgc=1, boundpoly has at least one root in (c,d)
# TranBound := proc(boundpoly, var, c, d)
# local tranpoly, deg, clist, sgc, signlist, i;
# deg      := degree(boundpoly);
# # print("deg", deg);
# tranpoly := expand(simplify((1+var[1])^deg * subs(var[1]=(c*var[1]+d)/(var[1]+1), boundpoly)));
# # print("tranpoly", tranpoly);
# clist    := [coeffs(tranpoly, var, 'mlist')];   
# # print("clist", clist);   
# signlist := [seq(sign(clist[i]), i=1..nops(clist))];
# # print("signlist", signlist);
# sgc      := SGCNum(signlist);
# return sgc;
# end proc:

##################### proc TranBoundRF
# TranBoundRF := proc(boundpoly, var, c, d)
# local deg, tranpoly, rootlist, i, temp;
# deg      := degree(boundpoly);
# # print("deg", deg);
# tranpoly := expand(simplify((1+var[1])^deg * subs(var[1]=(c*var[1]+d)/(var[1]+1), boundpoly)));
# rootlist := Isolate(tranpoly, var, 1, output=interval);
# for i from 1 to nops(rootlist) do
#     temp := op(2, rootlist[i]);
#     if temp[1]>0 then
#        return 1;
#     end if;
#     if temp[1]=0 and temp[2]>0 then
#        return 1;
#     end if;      
# end do;
# return 0;
# end proc:


##################### proc TranBoundRF2
TranBoundRF2 := proc(boundpoly, var, c, d,bc,bd)
local idex,rootlist, i, temp,dd,dd1,cc,cc1;
# deg      := degree(boundpoly);
# print("deg", deg);
# tranpoly := expand(simplify((1+var[1])^deg * subs(var[1]=(c*var[1]+d)/(var[1]+1), boundpoly)));
rootlist := Isolate(boundpoly, var, 1, output=interval);
idex:=-1;
# print(rootlist);
for i from 1 to nops(rootlist) do
   temp := op(2, rootlist[i]);
   if temp[1]>=c  then 
      idex:=i;
      break;
   end if; 
end do;
# print(idex,var);
cc:=bc;dd:=bd;
if idex>0 then
   temp := op(2, rootlist[idex]);
   if temp[2]<=d then
      return 1,c,d;
   elif temp[1]>=d then
      dd:=min(dd,temp[1]);
   elif sign(subs(var[1]=d,boundpoly))=sign(subs(var[1]=temp[1],boundpoly)) then
      dd:=d;
   else
      return 1,c,d;
   end if; 
end if;
# print(idex,var);
if idex>1 then
   temp := op(2, rootlist[idex-1]);
   if temp[2]<c then
      cc:=max(cc,temp[2]);
   elif temp[2]=c then 
      if temp[1]=temp[2] then 
         return 1,c,d;
      else
         cc:=c;
      end if;
   elif sign(subs(var[1]=c,boundpoly))=sign(subs(var[1]=temp[2],boundpoly)) 
     or (temp[2]>d and sign(subs(var[1]=d,boundpoly))=sign(subs(var[1]=temp[1],boundpoly)))
    then 
      cc:=c;
   else
      return 1,c,d;
   end if;
end if;
return 0,cc,dd;
end proc:


###################### proc TwoTypeTerm (ok)
# input:
# poly: in \Q[x,y]
# var: [x,y]
# output:
# ans1: the sum of positive terms in poly
# ans2: the sum of negative terms in poly
TwoTypeTerm := proc(poly, var)
local ans1, ans2, clist, i, mlist;
ans1 := 0; ans2 := 0;
# print(poly,var);
clist := [coeffs(expand(poly), var, 'mlist')];
mlist := [mlist];
# print(clist);
# print(mlist);
# print(type(clist,array));
for i from 1 to nops(clist) do
    if clist[i]>0 then
       ans1 := ans1 + clist[i]*mlist[i];
    end if;
    if clist[i]<0 then
       ans2 := ans2 + clist[i]*mlist[i];
    end if;
end do;
return ans1, ans2;
end proc:

# ###################### proc PosiTerm
# PosiTerm := proc(poly, var)
# local ans, clist, i, mlist;
# ans := 0; 
# clist := [coeffs(poly, var, 'mlist')];
# # print(clist);
# # print(type(clist,array));
# for i from 1 to nops(clist) do
#     if clist[i]>0 then
#        ans := ans + clist[i]*mlist[i];
#     end if;
# end do;
# return ans;
# end proc:

# ###################### proc NegaTerm
# NegaTerm := proc(poly, var)
# local ans, clist, i, mlist;
# ans := 0; 
# clist := [coeffs(poly, var, 'mlist')];
# # print(clist);
# # print(type(clist,array));
# for i from 1 to nops(clist) do
#     if clist[i]<0 then
#        ans := ans + clist[i]*mlist[i];
#     end if;
# end do;
# return ans;
# end proc:
######################proc getpi4x0
gettanx0totanpi4subx0:= proc(a)
   return (1-a)/(1+a);
end proc:

######################proc getpi4x0
#x0=pi/4-x
getpi4x0:= proc(poly,var)
option cache;
local ans,deg,z;
# print(poly);
# deg := degree(poly, var[2]);
# print(deg);
# ans := expand(simplify(expand(
   # subs(var[2]=(1-var[2])/(1+var[2]),var[1]=Pi/4-var[1], poly) * (1+var[2])^deg)));
ans:=numer(expand(subs(var[2]=(1-var[2])/(1+var[2]),var[1]=Pi/4-var[1], poly)));
# print(ans);
return ans;
end proc:
###################### proc ArctanTaylor (ok)
# input:
# poly: in \Q[x,y]
# var: [x,y]
# ranum: in \Q
# n: the number of terms of Taylor series
# output:
# ansmax: the upper polynomial \Q[Pi][y] for poly(rPi+arctan(y), y)
# ansmin: the lower polynomial \Q[Pi][y] for poly(rPi+arctan(y), y)
# f(r*pi+x,tan(x))   x 0,pi/4
# x0=pi/4-x          x0 0,pi/4   
# f(r*pi+pi/4-x0,tan(pi/4-x0))
# f(r*pi+pi/4-x0,(1-tan(x0))/(1+tan(x0)))
ArctanTaylor := proc(combpoly, var, n,c,isrechange:=true) 
local posipoly, negapoly, ansmax, ansmin, taylormax, taylormin,taylormax0, taylormin0, posi1, posi2, nega1, nega2, p1, z,deg;
ansmax := 0; ansmin := 0;
p1 := subs(arctan(var[2]) = z, combpoly);
# print("p1", p1);
if c>7/10 then
  deg := degree(p1, var[2]);
  p1 :=getpi4x0(p1,[z,var[2]]);
end if;
# print("p1", p1);

posipoly, negapoly := TwoTypeTerm(p1, [var[2], z, Pi]);
# print("posipoly", posipoly);
# print("negapoly", negapoly);
# taylormax0:=  subs(var[2]= c1,MTM:-taylor(arctan(var[2]), 4*n+2));
# taylormin0:=  subs(var[2]= c1,MTM:-taylor(arctan(var[2]), 4*n));
taylormin,taylormax := ArctanPolyInt(var[2],n);
# taylormax := MTM:-taylor(arctan(var[2]), 4*n+2, c1) -arctan(c1)+evalf(arctan(c1));
# taylormin := MTM:-taylor(arctan(var[2]), 4*n, c1)-arctan(c1)+evalf(arctan(c1));
# print("taylormax", taylormax);
# print("taylormin", taylormin);
posi1 := subs(z = taylormax, posipoly); 
posi2 := subs(z = taylormin, posipoly);
nega1 := subs(z = taylormax, negapoly);
nega2 := subs(z = taylormin, negapoly);
# print("posi1", posi1);
# print("posi2", posi2);
# print("nega1", nega1);
# print("nega2", nega2);
ansmin := expand(posi2 + nega1);
ansmax := expand(posi1 + nega2);
# print("ansmin",ansmin);
# print("ansmax",ansmax);
if c>7/10 and isrechange then
  return getpi4x0(ansmin,[z,var[2]]), getpi4x0(ansmax,[z,var[2]]);
else
  return ansmin,ansmax;
end if;
end proc:

###################### proc EstimatePi (ok)
# input:
# minpipoly: a lower polynomial in \Q[Pi,y]
# maxpipoly: an upper polynomial in \Q[Pi,y]
# pivar: [Pi,y]
# digit: decimal digits
# output:
# ansmin: the lower polynomial \Q[y] for minpipoly
# ansmax: the upper polynomial \Q[y] for maxpipoly
EstimatePi := proc(minpipoly, maxpipoly, pivar, digit)
local pimin, pimax, ansmin, ansmax;
pimin, pimax := ForPi(digit);
ansmin := EstimateMinPi(minpipoly, pimin, pimax, pivar);
ansmax := EstimateMaxPi(maxpipoly, pimin, pimax, pivar);
return ansmin, ansmax;
end proc:

###################### proc EstimateMinPi (ok)
EstimateMinPi := proc(minpipoly, pimin, pimax, pivar)
local posimin, negamin, posi2, nega1, ansmin;
# print("EstimateMinPi",minpipoly);
posimin, negamin := TwoTypeTerm(minpipoly, pivar);
# posi1 := subs(pivar[1] = pimax, posipoly); 
posi2 := subs(pivar[1] = pimin, posimin);
nega1 := subs(pivar[1] = pimax, negamin);
# nega2 := subs(pivar[1] = pimin, negapoly);
# ansmax := expand(posi1 + nega2);
ansmin := expand(posi2 + nega1);
return ansmin;
end proc:

###################### proc EstimateMaxPi (ok)
EstimateMaxPi := proc(maxpipoly, pimin, pimax, pivar)
local posimax, negamax, posi1, nega2, ansmax;
posimax, negamax := TwoTypeTerm(maxpipoly, pivar);
posi1 := subs(pivar[1] = pimax, posimax); 
# posi2 := subs(pivar[1] = pimin, posipoly);
# nega1 := subs(pivar[1] = pimax, negapoly);
nega2 := subs(pivar[1] = pimin, negamax);
ansmax := expand(posi1 + nega2);
# ansmin := expand(posi2 + nega1);
return ansmax;
end proc:

# ###################### proc ForPi (ok)
# # input
# # digit=1, return 3.1, 3.2; digit=2, return 3.14, 3.15;...
# ForPi := proc(digit)
# local a, ansmin, ansmax;
# # a := 31415926535;
# if digit>200 then
#    error "FAIL: We can not approximate Pi to more than 200 digits.";  
# end if;
# a := 314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196;
# ansmin := iquo(a, 10^(200-digit))/10^(digit);
# ansmax := (iquo(a, 10^(200-digit))+1)/10^(digit);
# return ansmin, ansmax;
# end proc:

###################### proc ForPi (ok)
# input
# digit=1, return 31/10, 32/10; digit=2, return 314/100, 315/100;...
ForPi := proc(digit)
local a, ansmin, ansmax, num;
# a := 31415926535;
# if digit>200 then
#    error "FAIL: We can not approximate Pi to more than 200 digits.";  
# end if;
if digit<=50 then
num := 50;
a := 314159265358979323846264338327950288419716939937510;
ansmin := iquo(a, 10^(num-digit))/10^(digit);
ansmax := (iquo(a, 10^(num-digit))+1)/10^(digit);
elif digit<=200 then
num := 200;
a := 314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196;
ansmin := iquo(a, 10^(num-digit))/10^(digit);
ansmax := (iquo(a, 10^(num-digit))+1)/10^(digit);
elif digit<=500 then
num:=500;
a:=314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458700660631558817488152092096282925409171536436789259036001133053054882046652138414695194151160943305727036575959195309218611738193261179310511854807446237996274956735188575272489122793818301194912;
ansmin := iquo(a, 10^(num-digit))/10^(digit);
ansmax := (iquo(a, 10^(num-digit))+1)/10^(digit);
elif digit<=1000 then
num:=1000;
a:=31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679821480865132823066470938446095505822317253594081284811174502841027019385211055596446229489549303819644288109756659334461284756482337867831652712019091456485669234603486104543266482133936072602491412737245870066063155881748815209209628292540917153643678925903600113305305488204665213841469519415116094330572703657595919530921861173819326117931051185480744623799627495673518857527248912279381830119491298336733624406566430860213949463952247371907021798609437027705392171762931767523846748184676694051320005681271452635608277857713427577896091736371787214684409012249534301465495853710507922796892589235420199561121290219608640344181598136297747713099605187072113499999983729780499510597317328160963185950244594553469083026425223082533446850352619311881710100031378387528865875332083814206171776691473035982534904287554687311595628638823537875937519577818577805321712268066130019278766111959092164201989;
ansmin := iquo(a, 10^(num-digit))/10^(digit);
ansmax := (iquo(a, 10^(num-digit))+1)/10^(digit);
else 
error "FAIL: We can not approximate Pi to more than 1000 digits."; 
end if;
return ansmin, ansmax;
end proc:

###################### proc BoundPoly (ok)
BoundPoly := proc(combpoly, var, n, digit,cc,isrechange:=true)
local min1, max1, ansmin, ansmax;
min1, max1 := ArctanTaylor(combpoly, var, n,cc,isrechange);
# print("arctanmin", min1);
# print("arctanmax", max1);
ansmin, ansmax := EstimatePi(min1, max1, [Pi, var[2]], digit);
# print("ansmin", ansmin);
# print("ansmax", ansmax);
#--print("BoundPoly ArctanTaylor done.");#--

return ansmin, ansmax;
end proc:

###################### proc IBR
# The procedure IBR is Algorithm 4 in our paper.
# input: 
# poly: an irreducible polynomial in \Q[x,y] with \deg(poly, y)\ge1
# var: [x,y]
# intk: in \Z 
# output: 
# the set of isolating cubes of real roots of g(x,\tan{x}) in (intk*Pi - Pi/2, intk*Pi + Pi/2)
IBR := proc(pseq, wseq, var, intk, nstart:=3, nstep:=3,eps:=1)
local tranpoly, s1, s2, element, p1, p2, p3, ans, st, r1, r2, r3, r4;
# p1 := subs([var[1] = intk*Pi - (Pi/4), var[2] = -1], pseq[3]);
# p2 := subs([var[1] = intk*Pi, var[2] = 0], pseq[3]);
# p3 := subs([var[1] = intk*Pi + (Pi/4), var[2] = 1], pseq[3]); 
### poly(x,tanx) on (k*Pi-Pi/2, k*Pi-Pi/4)
s1 := SubIBR(wseq[1], var, -intk + (1/4), nstart, nstep, eps);  
r1 := []; 
for element in s1 do 
   r1 := [[-element[2], -element[1]], op(r1)]; 
end do;
#--print("r1", r1);#--
### poly(x,tanx) on (k*Pi-Pi/4, k*Pi)
s2 := SubIBR(wseq[2], var, -intk, nstart, nstep, eps);  
r2 := [];
for element in s2 do 
   r2 := [[-element[2], -element[1]], op(r2)]; 
end do;
#--print("r2", r2);#--
### poly(x,tanx) on (k*Pi, k*Pi+Pi/4)
r3 := SubIBR(wseq[3], var, intk, nstart, nstep, eps);
#--print("r3", r3);#--
### poly(x,tanx) on (k*Pi+Pi/4, k*Pi+Pi/2)
r4 := SubIBR(wseq[4], var, intk + (1/4), nstart, nstep, eps);
#--print("r4", r4);#--
ans := r1;
# if p1=0 then ans := [op(ans), [intk*Pi-Pi/4, intk*Pi-Pi/4]]; end if;
ans := [op(ans), op(r2)];
# if p2=0 then ans := [op(ans), [intk*Pi, intk*Pi]]; end if;
ans := [op(ans), op(r3)];
# if p3=0 then ans := [op(ans), [intk*Pi+Pi/4, intk*Pi+Pi/4]]; end if;
ans := [op(ans), op(r4)];
return ans;
end proc:

###################### proc PreProc
PreProc := proc(poly, var)
local d, poly1, poly2, poly3, poly4, wseq1, wseq2, wseq3, wseq4, pseq, wseq,ans;
d := degree(poly, var[2]);
if d=0 then
   error "FAIL: The degree of the input polynomial w.r.t. var[2] is 0.";
end if;
poly2 := subs([var[1] = -var[1], var[2] = -var[2]], poly);
# poly1 := expand(simplify(subs(var[2]=(1+var[2])/(1-var[2]), poly2) * (1-var[2])^(d)));
poly1 :=expand( numer(expand(subs(var[2]=(1+var[2])/(1-var[2]), poly2))));
poly3 := poly;
# poly4 := expand(simplify(subs(var[2]=(1+var[2])/(1-var[2]), poly) * (1-var[2])^(d)));
poly4 := expand(numer(expand(subs(var[2]=(1+var[2])/(1-var[2]), poly))));
pseq  := [poly1, poly2, poly3, poly4];
ans,wseq1 := WeakFourierSeq(poly1, var);
ans,wseq2 := WeakFourierSeq(poly2, var);
ans,wseq3 := WeakFourierSeq(poly3, var);
ans,wseq4 := WeakFourierSeq(poly4, var);
wseq  := [wseq1,wseq2,wseq3,wseq4];
# print("Case 1:", pseq[1], wseq[1]);
# print("Case 2:", pseq[2], wseq[2]);
# print("Case 3:", pseq[3], wseq[3]);
# print("Case 4:", pseq[4], wseq[4]);
return pseq, wseq;
end proc:

###################### proc mainIBR
# input:
# poly: an irreducibile polynomial in \Q[x,y] \setminus {0}
# var: [x,y]
# kmin, kmax: two integers where kmin <= kmax
# output:
# if deg(poly)=0 and poly<>0, the output is []
# if deg(poly, y)=0, the output is a list of all real roots of poly(x) on \R
# if deg(poly, x)=0, the output is a list of all real roots of poly(tan(x)) on 
#                    the open interval (kmin*Pi-Pi/2, kmax*Pi+Pi/2) \setminus {k*Pi-Pi/2, k*Pi+Pi/2 | kmin <= k <= kmax}
# otherwise, the output is a list of real roots of poly(x, tan(x)) on 
#                    the open interval (kmin*Pi-Pi/2, kmax*Pi+Pi/2) \setminus {k*Pi-Pi/2, k*Pi+Pi/2 | kmin <= k <= kmax}
mainIBR := proc(poly, var, kmin, kmax, nstart:=3, nstep:=3, eps:=1)
local ans, anslen,i, templist, pseq, wseq, st, rootlist, temp, j;
ans :=  Vector[row]();
anslen:=0;
if kmin>kmax then
   error "FAIL: The input kmax is greater than the input kmin.";
end if;
if poly=0 then
   error "FAIL: The input polynomial is 0.";
elif degree(poly)=0 then
   return [];
elif degree(poly, var[2])=0 then
   return Isolate(poly, [var[1]], 1, output=interval);
elif degree(poly, var[1])=0 then
   rootlist := Isolate(poly, [var[2]], 1, output=interval);
   for j from kmin to kmax do
      for i from 1 to nops(rootlist) do
         temp := op(2, rootlist[i]);
         anslen :=anslen+1;
         ans(anslen)  :=  [j*Pi+arctan(temp[1]), j*Pi+arctan(temp[2])];
      end do;
   end do;
   return ans;
end if;
printf("开始计算弱傅里叶序列\n"); 
# try
#    st := time[real]():
#    timelimit[real](3600, print(time[real](PreProc(poly, var))));
# catch:
# print("计算弱傅里叶序列超时", time[real]()-st);      
# end try; 
st := time[real]():  
pseq, wseq := PreProc(poly, var);
printf("弱傅里叶序列的长度: %a,%a,%a,%a,%a\n", nops(wseq[1]), nops(wseq[2]), nops(wseq[3]), nops(wseq[4]),time[real]()-st); 
for i from kmin to kmax do
#--   print("the i-th time:", i);#--
#--   st := time[real]():#--
   templist := IBR(pseq, wseq, var, i, nstart, nstep, eps);
#--   print("the time of i-th:", time[real]()-st);#--
#--   print("the i-th result", templist);#--
   for temp in templist do
      anslen :=anslen+1;
      ans(anslen) := temp;
   end do;
end do;
return ans;
end proc:
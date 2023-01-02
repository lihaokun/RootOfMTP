#### @author Tianqi Zhao  Haokun Li

read "mainIBR.mpl";

with(RootFinding):



###################### proc TranMTPToPoly
TranMTPToPoly := proc(poly, var, varsin, varcos)
local ans;
ans := subs([sin(var)=varsin, cos(var)=varcos, tan(var)=varsin/varcos, csc(var)=1/varsin, sec(var)=1/varcos, cot(var)=varcos/varsin], poly);
end proc:



###################### proc FindFactor
FindFactor := proc(poly1, poly2)
local factorlist, fac, ans;
factorlist := factors(poly1);
for fac in factorlist[2] do
    if fac[1]=poly2 then
       return fac[2];     
    end if;
end do;
return 0;
end proc:

###################### proc FindUnipoly
FindUnipoly := proc(poly, var)
local factorlist, fac, ans;
factorlist := factors(poly);
ans := [];
for fac in factorlist[2] do
    if degree(fac[1], var[1])=0 then
       ans := [op(ans), [fac[1], fac[2]]];     
    end if;
end do;
return ans;
end proc:
########################### proc FindUnipoly2
FindUnipoly2 := proc(poly, var)
local factorlist, fac, xpoly,ypoly;
factorlist := factors(poly);
xpoly := [];
ypoly := [];
for fac in factorlist[2] do
    if degree(fac[1], var[1])=0 then
        ypoly := [op(ypoly), [fac[1], fac[2]]];     
    elif degree(fac[1], var[2])=0 then
        xpoly := [op(xpoly), [fac[1], fac[2]]];   
    end if;

end do;
return xpoly,ypoly;
end proc:
############## proc RefinePoly
# poly: in Q[t]
# var: t
RefinePoly := proc(poly, var, c1, d1)
local left, mid, cc, dd, q;
cc := c1; dd := d1;
q := (cc+dd)/2;
left := sign(subs(var=cc, poly));
mid  := sign(subs(var=q, poly));
if mid=0 then   
   cc := q; dd := q;  
elif left * mid = -1 then
   dd := q;    
else
   cc := q;     
end if;
return cc,dd;
end proc:

############## proc RootBound
RootBound := proc(poly, var)
local rootlist, upper, low;
rootlist := Isolate(poly, [var], 1);
if nops(rootlist)=0 then
   return -1, 1;
else
   upper := ceil(op(2, rootlist[-1]));
   if upper<=0 then
      upper:=1;
   end if;
   low := floor(op(2, rootlist[1]));;
   if low>=0 then
      low:=-1;
   end if;
   return low, upper;
end if;
end proc:

############## proc NewBound
NewBound := proc(intermid, eps, dir)
local l,r,m;
l := dir;
r := 0;
if dir<>-1 and dir<>1 then
   error("NewBound的dir必须为1或-1.");
end if;
if evalf(abs(arctan(intermid)+ eps*dir) - Pi/2) > 0 then
   return intermid+1000*dir;
end if;
while evalf(abs(arctan(l+intermid)-arctan(intermid)) - eps)<0 do
     r := l; l := 2*l;
end do;
# print(l);
while evalf(abs(arctan(l+intermid)-arctan(intermid+r)) - eps*0.01)>0 do
    m := (l+r)/2;
    if evalf(abs(arctan(m+intermid)-arctan(intermid)) - eps)<0 then
        r := m;
    else
       l := m;
    end if;
end do;
return r+intermid;
end proc:

############## proc NewBoundInf
NewBoundInf := proc(up, eps, dir)
local l,r,m;
l := eps*dir;
r := 0;
if dir<>-1 and dir<>1 then
    error("NewBound的dir必须为1或-1.");
end if;
if evalf(abs(arctan(up)+ eps*dir) - Pi/2) > 0 then
    return up;
end if;
while evalf(Pi/2-abs(arctan(l+up)) -eps)>0 do
    r:=l;
    l := 2*l;
end do;
# print(l);
while evalf(abs(arctan(l+up)-arctan(r+up)) - eps*0.01)>0 do
    m := (l+r)/2;
    if evalf(Pi/2-abs(arctan(m+up)) -eps)>0 then
        r := m;
    else
        l := m;
    end if;
end do;
return l+up;
end proc:

###################### proc testtanpolyrootnum
TestTanPolyRootNum:=proc(tanpoly,var,infrootinter,x0)
    local multilist,multitable,i,tanpolyfac,roottemp,j,temp,intertemp,ploytemp,isfind;
    multilist:=[];multitable:=[];
    tanpolyfac:= op(2,factors(tanpoly));
    for i in infrootinter do
        multilist:=[op(multilist),[]];
        multitable:=[op(multitable),table()];
    end do;
    for i in tanpolyfac do
        ploytemp:=subs(var[1]=x0,i[1]);
        # print(ploytemp);
        roottemp:=Isolate(ploytemp, [var[2]],3,output=interval);
        j:=1;
        for temp in roottemp do
            isfind:=false;
            intertemp := op(2, temp); 
            while true do
                if j>nops(infrootinter) then
                    error("发现了无法分类的根，潜在区间错误!");
                end if;
                if infrootinter[j][1]<>infrootinter[j][2]  then
                    if  intertemp[1]>=infrootinter[j][2] then
                        j:=j+1;
                    elif  intertemp[2]<=infrootinter[j][1] then
                        error("发现了无法分类的根，潜在区间错误!");
                    elif intertemp[1]>infrootinter[j][1] and intertemp[2]<infrootinter[j][2] then
                        isfind:=true;
                        break;
                    end if;
                    intertemp:=[RefinePoly(ploytemp,var[2],intertemp[1], intertemp[2])];
                else
                    if intertemp[2]<infrootinter[j][1]
                    or (intertemp[1]<>intertemp[2] and intertemp[2]=infrootinter[j][1])
                    then
                        error("发现了无法分类的根，潜在区间错误!");
                    elif  intertemp[1]>infrootinter[j][2]
                        or (intertemp[1]<>intertemp[2] and intertemp[1]=infrootinter[j][2])
                     then
                        j:=j+1;
                    elif intertemp[1]=infrootinter[j][2]  and  intertemp[1]=intertemp[2] then
                        isfind:=true;
                        break;
                    else 
                        if subs(var[2]=intertemp[1],ploytemp)=0 then
                            intertemp:=[intertemp[1],intertemp[1]];
                            isfind:=true;
                            break;
                        end if;
                        j:=j+1;
                    end if;
                end if;
            end do;
            if isfind then
                if assigned(multitable[j][i[2]]) then
                    multitable[j][i[2]]:=multitable[j][i[2]]+1;
                else
                    multitable[j][i[2]]:=1;
                    multilist[j]:=[op(multilist[j]),i[2]];
                end if;
            end if;
        end do;
    end do;
    return multilist,multitable;
end proc:


###################### proc RootOfMTP
# MTP: a rational function f(x, x1, x2, x3, x4, x5, x6) in Q(x, x1, x2, x3, x4, x5, x6), 
#      where x1=sin(x), x2=cos(x), x3=tan(x), x4=csc(x), x5=sec(x), x6=cot(x)
# var: x
# eps: default 1
RootOfMTP := proc(MTP, var, eeps:=1)
local poly, vc, vs, t, cotpoly, temp, tanpoly,xfactor, element, roottemp, tempnum, tfactor, i, tlcoeff, intertemp, infrootmid, eps,
infrootinter, mid, left, low, upper, temp1, temp2, newleft, right, runtimes, runtimesb, newleft1, tanpolyfac, klow, kupper,temptable, 
templist, multilist, multitable, fac, temproot,deta1,deta2,hpoly,dpoly,ans1,ans2,ans1len,ans2len;
ans1:= Vector[row]();
ans2:= Vector[row]();
ans1len:=0;ans2len:=0;
runtimesb := 6; 
eps := eeps;
poly := Numerator(TranMTPToPoly(MTP, var, vs, vc));
# 这里, poly in Q[x, vs, vc].
printf("poly: %a\n", subs([vs=sin(var),vc=cos(var)],poly));
cotpoly := simplify(subs([var=2*var, vs=(2*t/(1 + t^2)), vc=((t^2 - 1)/(1 + t^2))], poly) * (1 + t^2)^degree(poly, [vs, vc]));
# 这里, poly in Q[x, vs, vc] => cotpoly in Q[x, t] and t represents cot(x).
# print("cotpoly", cotpoly);
if cotpoly=0 then
   printf("MTP恒等于0.\n");
   return;
end if;
temp := FindFactor(cotpoly, t);
# 这里, cotpoly = t^(temp) * (a polynomial in Q[x, t]).
if temp<>0 then
    # print(1, "root in ", k*Pi+Pi/2, "(k in Z)", "重数:", temp);
    InfRootOutput(1, temp, [infinity, infinity]);
    # 测试 k*Pi+Pi/2 位点
end if;
# tanpoly := expand(simplify(expand(simplify(subs([var=2*var, vs=(2*t/(1 + t^2)), vc=((1 - t^2)/(1 + t^2))],expand(poly)) * (1 + t^2)^degree(poly, [vs, vc])))));
# st:=time[real]();
tanpoly:=numer(subs([var=2*var, vs=(2*t/(1 + t^2)), vc=((1 - t^2)/(1 + t^2))],expand(poly)));
# print(time[real]()-st);
# 这里, poly in Q[x, vs, vc] => tanpoly in Q[x, t] and t represents tan(x).
# tanpoly := 48*var^4*t^8 + 64*var^2*t^10 + 48*var^6*t^5 + 40*var^4*t^7 - 160*var^2*t^9 - 24*var^6*t^4 - 157*var^4*t^6 - 48*var^3*t^7 + 132*var^2*t^8 - 64*var*t^9 + 3*var^6*t^3 - 48*var^5*t^4 + 132*var^4*t^5 - 52*var^3*t^6 - 44*var^2*t^7 + 144*var*t^8 + 12*var^5*t^3 - 44*var^4*t^4 + 192*var^3*t^5 + 5*var^2*t^6 - 32*var*t^7 + 48*var^5*t^2 + 5*var^4*t^3 - 56*var^3*t^4 - 140*var*t^6 - 24*var^5*t - 137*var^3*t^3 - 48*var^2*t^4 + 132*var*t^5 - 64*t^6 + 3*var^5 - 48*var^4*t + 180*var^3*t^2 - 52*var^2*t^3 + 20*var*t^4 + 144*t^5 + 12*var^4 - 68*var^3*t + 144*var^2*t^2 - 155*var*t^3 - 96*t^4 + 8*var^3 - 144*var^2*t + 132*var*t^2 - 44*t^3 + 32*var^2 - 44*var*t + 144*t^2 + 5*var - 96*t + 20;
# tanpoly := var^5 + t*var^2 + (t+2)^3*var + t^3-1;
printf("tanpoly %a\n", tanpoly);
eps := eps/2;
xfactor,temp := FindUnipoly2(tanpoly, [var, t]);
# print (xfactor,temp);
# 这里, temp 是 tanpoly 的只含 t 的所有因子的列表.
# 这里, xfactor 是 tanpoly 的只含 x 的所有因子的列表.
tfactor := 1;
for element in temp do
    tfactor := tfactor * element[1]^(element[2]);
    if element[1]=t then
        # print(1, "root in ", k*Pi, "(k in Z and k<>0)", "重数:", element[2]);
        InfRootOutputk(1, element[2], [0,0], -1);
        InfRootOutputk(1, element[2], [0,0], 1);
        # 测试 k*Pi 位点, k<>0. 后面单独处理 k=0 的情况.
    elif element[1]=t-1 then
        # print(1, "root in ", k*Pi+Pi/4, "(k in Z)", "重数:", element[2]);
        InfRootOutput(1, element[2], [1,1]);
        # 测试 k*Pi+Pi/4 位点
    elif element[1]=t+1 then
        # print(1, "root in ", k*Pi-Pi/4, "(k in Z)", "重数:", element[2]);
        InfRootOutput(1, element[2], [-1,-1]);
        # 测试 k*Pi-Pi/4 位点
    else
        roottemp := Isolate(element[1], [t], 1, output=interval);
        for i from 1 to nops(roottemp) do
            intertemp := op(2, roottemp[i]);
            while evalf(abs(arctan(intertemp[2])-arctan(intertemp[1]))-eps)>0 do
                intertemp := [RefinePoly(element[1], t, intertemp[1], intertemp[2])];
                # 对于一个不可约的多项式 f(x,y) in Q[x,y], f(x,tan(x)) 的根都是单根.
            end do;
            if intertemp[2]=intertemp[1] then
                # print(1, "root in ", k*Pi+arctan(intertemp[1]), "(k in Z)", "重数:", element[2]);
                InfRootOutput(1, element[2], [intertemp[1], intertemp[1]]);
            else
                # print(1, "root in ", (k*Pi+arctan(intertemp[1]), k*Pi+arctan(intertemp[2])), "(k in Z)", "重数:", element[2]);
                InfRootOutput(1, element[2], [intertemp[1], intertemp[2]]);
            end if;         
      end do;
    end if;
end do;
for element in xfactor do
    tfactor := tfactor * element[1]^(element[2]);
end do;
temp := subs(t=tan(var), tanpoly);
# 这里, temp 是 tanpoly(x, tan(x)).
tempnum := 0;
# print("temp", temp);
while subs([tan(var)=0,var=0], temp)=0 do
    tempnum := tempnum + 1;
    temp := diff(temp, var);
    # print("temp", temp);
end do;
if tempnum<>0 then
    # print(1, "root in ", 0, "重数:", tempnum);
    OneRootOutput(1, tempnum, [0,0]);
end if;
tanpoly := simplify(tanpoly/tfactor);
printf("tanpoly_xt: %a\n", tanpoly);
tanpoly := simplify(tanpoly/gcd(tanpoly, diff(tanpoly,t)));
# tanpoly := simplify(tanpoly/gcd(tanpoly, diff(tanpoly,var)));
# 处理 tanpoly 的既含 x 又含 t 的全部因子
printf("tanpoly_xt: %a\n", tanpoly);
if  degree(tanpoly, var)<>0 then 
    tlcoeff := lcoeff(tanpoly, var);
    # 这里, tlcoeff 是 tanpoly 的关于 x 的首项系数.
    # print("tlcoeff", tlcoeff);
    tlcoeff := simplify(tlcoeff/gcd(tlcoeff, diff(tlcoeff,t)));
    # 这里, tlcoeff 是 (tanpoly 的关于 x 的首项系数) 的无平方部分, 故 tlcoeff \in \Q[t].
    # print("sf-tlcoeff", tlcoeff);
    # if degree(tlcoeff, t)<>0  then
    roottemp := Isolate(tlcoeff, [t], 3, output=interval);
    # print("roottemp", roottemp);
    # print("nops(roottemp)", nops(roottemp));
    infrootmid := [];
    for i from 1 to nops(roottemp) do
        intertemp := op(2, roottemp[i]);
        # if intertemp[2]=intertemp[1] then
        #    intertemp[1] := intertemp[1]-max(2*eps,1);
        #    intertemp[2] := intertemp[2]+max(2*eps,1);
        # end if;
        while evalf(abs(arctan(intertemp[2])-arctan(intertemp[1]))-eps)>0 do
            intertemp := [RefinePoly(tlcoeff, t, intertemp[1], intertemp[2])];
            # print("intertemp", intertemp);
        end do;   
        infrootmid := [op(infrootmid), [intertemp[1],intertemp[2]]];
    end do;
    if nops(roottemp)>0 then
        newleft1 := NewBoundInf(infrootmid[1][1], eps/2, -1); 
        # newleft := NewBoundInf(infrootmid[-1][1], eps/2, 1); 
    else
        newleft1 := NewBoundInf(0, eps/2, -1); 
        # newleft := NewBoundInf(10, eps/2, -1); 
    end if;
    infrootmid := [[-infinity, -infinity], op(infrootmid)];
    infrootinter := [[-infinity, newleft1]];
    # print("infrootinter", infrootinter);
    for i from 2 to nops(infrootmid) do
        mid := (infrootmid[i][1]+infrootmid[i][2])/2;
        left := min(NewBound(mid,eps/2,-1), infrootmid[i][1]);
        if left<infrootmid[i-1][2] then
            left := infrootmid[i-1][2];
        end if;
        if left<infrootinter[i-1][2] then
            newleft:=(left+infrootinter[i-1][2])/2;
            runtimes := 0;
            while true do
                runtimes := runtimes +1;
                low, upper := RootBound(subs(t=newleft,tanpoly), var);
                temp := upper-low;
                low, upper := RootBound(subs(t=(newleft+left)/2,tanpoly), var);
                temp1 := upper-low;
                low, upper := RootBound(subs(t=(newleft+infrootinter[i-1][2])/2,tanpoly), var);
                temp2 := upper-low;
                if (temp>temp1) then
                    newleft:=(newleft+left)/2;
                elif (temp>temp2) then
                    newleft:=(newleft+infrootinter[i-1][2])/2;
                end if;
            # until temp<=min(temp1,temp2) or runtimes>runtimesb;
                if temp<=min(temp1,temp2) or runtimes>runtimesb then
                    break;
                end if;
            end do;
            left := newleft;
            infrootinter[i-1][2]:=left;
        end if;
        right := max(NewBound(mid,eps/2,1), infrootmid[i][2]);
        infrootinter := [op(infrootinter), [left,right]];
        # print(left, right);
    end do;
    if nops(roottemp)>0 then
        newleft1 := NewBoundInf(infrootmid[-1][1], eps/2, 1); 
        # newleft := NewBoundInf(infrootmid[-1][1], eps/2, 1); 
    else
        newleft1 := NewBoundInf(0, eps/2, 1); 
        # newleft := NewBoundInf(10, eps/2, -1); 
    end if;
    # print("newleft1", newleft1);
    # newleft1 := NewBoundInf(infrootmid[-1][2], eps/2, 1);  
    # print("nops(roottemp)", nops(roottemp));
    if nops(roottemp)>0 then
        left := infrootinter[-1][2];
        if left>newleft1 then
            newleft := (left+newleft1)/2;
            runtimes := 0;
            while true do
                runtimes := runtimes +1;
                low, upper := RootBound(subs(t=newleft,tanpoly), var);
                temp := upper-low;
                low, upper := RootBound(subs(t=(newleft+left)/2,tanpoly), var);
                temp1 := upper-low;
                low, upper := RootBound(subs(t=(newleft+newleft1)/2,tanpoly), var);
                temp2 := upper-low;
                if (temp>temp1) then
                    newleft:=(newleft+left)/2;
                elif (temp>temp2) then
                    newleft:=(newleft+newleft1)/2;
                end if;
                if (temp<=min(temp1,temp2) or runtimes>runtimesb) then
                    break;
                end if;
            end do;
            # until temp<=min(temp1,temp2) or runtimes>runtimesb;
            infrootinter[-1][2] := newleft;
            newleft1 := newleft;
        end if;
    end if;
    infrootinter := [op(infrootinter), [newleft1,infinity]];
    # else
    #     infrootinter:=[];
    # end if;
    # print("tanpoly", tanpoly);
    # print("gcd(tanpoly, diff(tanpoly,var))",gcd(tanpoly, diff(tanpoly,var)));
    temp := simplify(tanpoly/gcd(tanpoly, diff(tanpoly,var)));
    # print("tanpoly/gcd(tanpoly, diff(tanpoly,var))", temp);
    # print("discrim(temp,t)", discrim(temp,t));
    low,upper := RootBound(discrim(temp,t),var);
    temp1,temp2 := RootBound(lcoeff(tanpoly,t),var);
    low := min(low, temp1); upper := max(upper, temp2);
    # print("factors(tanpoly)", factors(tanpoly));
    # print("tanpolyfac", tanpolyfac);
    for element in infrootinter do
        if element[1]<>-infinity then
        temp1,temp2 := RootBound(subs(t=element[1],tanpoly),var);
        low := min(low, temp1); upper := max(upper, temp2);
        end if;
        if element[2]<>infinity then
            temp1,temp2 := RootBound(subs(t=element[2],tanpoly),var);
            low := min(low, temp1); upper := max(upper, temp2);
        end if;
    end do;

    printf("low: %a, upper: %a.\n", low, upper);
    deta1:=999;deta2:=1000;
    temp1:=diff(tanpoly,var);
    temp2:=diff(tanpoly,t);
    while true do
        dpoly:=expand(resultant(temp1+(deta1/deta2)*temp2,tanpoly,t));
        if dpoly<>0 then
            break;
        end if;
        deta1:=deta1*10+9;
        deta2:=deta2*10;
    end do;
    printf("deta: %a \n",deta1/deta2);
    temp1,temp2 := RootBound(dpoly,var);
    low := min(low, temp1); upper := max(upper, temp2);
    
    hpoly:=expand(subs(t=1/t,tanpoly)*t^degree(tanpoly,t));
    printf("hpoly: %a\n",hpoly);
    temp1:=diff(hpoly,var);
    temp2:=diff(hpoly,t);
    deta1:=999;deta2:=1000;
    while true do
        dpoly:=expand(resultant(temp1-(deta1/deta2)*temp2,hpoly,t));
        if dpoly<>0 then
            break;
        end if;
        deta1:=deta1*10+9;
        deta2:=deta2*10;
    end do;
    printf("deta: %a \n",deta1/deta2);
    temp1,temp2 := RootBound(dpoly,var);
    low := min(low, temp1); upper := max(upper, temp2);
    temp1,temp2 := RootBound(discrim(hpoly,t),var);
    low := min(low, temp1); upper := max(upper, temp2);
    temp1,temp2 := RootBound(lcoeff(hpoly,t),var);
    low := min(low, temp1); upper := max(upper, temp2);
    printf("low: %a, upper: %a \n", low, upper);

    printf("infrootinter: %a\n",infrootinter);
    klow := floor((low+Pi/2)/Pi);
    kupper := ceil((upper-Pi/2)/Pi);
    printf("klow, kupper: %a,%a\n", klow, kupper);
    multilist,multitable:=TestTanPolyRootNum(tanpoly,[var,t],infrootinter,upper+1);
    for i from 1 to nops(infrootinter) do
        for temp in multilist[i] do
            InfRootOutputk(multitable[i][temp],temp,[infrootinter[i][1], infrootinter[i][2]],kupper+1);
        end do;
    end do;
    multilist,multitable:=TestTanPolyRootNum(tanpoly,[var,t],infrootinter,low-1);
    for i from 1 to nops(infrootinter) do
        for temp in multilist[i] do
            InfRootOutputk(multitable[i][temp],temp,[infrootinter[i][1], infrootinter[i][2]],klow-1);
        end do;
    end do;
    tanpolyfac:= op(2,factors(tanpoly));
    # boundroot := [];
    for fac in tanpolyfac do
        #  print\("###########################");
        printf("irreducible factor: %a\n", fac[1]);
        temproot := mainIBR(fac[1], [var,t], klow, kupper, 3, 3, eps);
        if temproot<>[] then
            OneRootOutputList(1, fac[2], temproot);
        end if;
        # boundroot := [op(boundroot), op(temproot)];
    end do;
end if;
temp1:=ceil(log10(1/eps));
if temp1<0 then
    temp1:=0;
end if;
for element in xfactor do
    if element[1]<>var then
        # print(element,var,temp1);
        roottemp:=Isolate(element[1], [var], temp1, output=interval);
        temproot:=[];
        for temp in roottemp do
            temproot := [op(temproot),op(2, temp)];
        end do;
        # print("temproot:", temproot);
        if temproot<>[] then
            OneRootOutputList(1, element[2], temproot);
        end if;
    end if;
end do;
end proc:


# out: ((2kPi+2*arctan(l),2kPi+2*arctan(r)), num,multi,k>=a(k\in z))  (a>=0) 
# ans: ((2*arctan(l),2*arctan(r)), num,multi,a)
# out: ((2kPi+2*arctan(l),2kPi+2*arctan(l)), num,multi,k<=a(k\in z))  (a<0) 
# ans: ((2*arctan(l),2*arctan(l)), num,multi,a)
# out: ((2kPi+2*arctan(l),2kPi+2*arctan(l)), num,multi,(k\in z))  
# ans: ((2*arctan(l),2*arctan(l)), num,multi,0) ,((2*arctan(l),2*arctan(l)), num,multi,-1)

# out: ((l,r)),multi) 
# ans:((l,r)),multi) 



######### proc InfRootOutput
InfRootOutput := proc(num, multi, inte)
# local ;
if inte[1]=inte[2] then 
    printf("For every k (k in Z), 2k%a+(%a) is a real root with multiplicity %a.\n", Pi, 2*arctan(inte[1]), multi);
    #    printf("x/2 在 [k%a+(%a)], k \in \Z 中有 %a 个 %a 重根\n", Pi, arctan(inte[1]), num, multi);
else 
    if num=1 then
      printf("For every k (k in Z), there is a real root with multiplicity %a in (2k%a+(%a), 2k%a+(%a)).\n", multi, Pi,2*arctan(inte[1]), Pi, 2*arctan(inte[2]));
    else
      printf("For every k (k in Z), there are %a real roots with multiplicity %a in (2k%a+(%a), 2k%a+(%a)).\n", num, multi, Pi, 2*arctan(inte[1]), Pi, 2*arctan(inte[2]));
    end if;   
    #    printf("x/2 在 (k%a+(%a), k%a+(%a)), k \in \Z 中有 %a 个 %a 重根\n", Pi, arctan(inte[1]), Pi, arctan(inte[2]), num, multi);
end if; 
end proc:

######### proc InfRootOutputk
InfRootOutputk := proc(num, multi, inte, k)
# local ;
if k>=0 then
    if inte[1]=inte[2] then
        printf("For every k >= %a (k in Z), 2k%a+(%a) is a real root with multiplicity %a.\n", k, Pi, 2*arctan(inte[1]), multi);
        # printf("x/2 在 [k%a+(%a)], k >= %a (k \in \Z) 中有 %a 个 %a 重根\n", Pi, arctan(inte[1]), k, num, multi);
    else 
        if num=1 then
            printf("For every k >= %a (k in Z), there is %a real root with multiplicity %a in (2k%a+(%a), 2k%a+(%a)).\n", k, num, multi, Pi, 2*arctan(inte[1]), Pi, 2*arctan(inte[2]));
        else
            printf("For every k >= %a (k in Z), there are %a real roots with multiplicity %a in (2k%a+(%a), 2k%a+(%a)).\n", k, num, multi, Pi, 2*arctan(inte[1]), Pi, 2*arctan(inte[2]));
        end if;  
        # printf("x/2 在 (k%a+(%a), k%a+(%a)), k >= %a (k \in \Z) 中有 %a 个 %a 重根\n", Pi, arctan(inte[1]), Pi, arctan(inte[2]), k, num, multi);
    end if; 
else
    if inte[1]=inte[2] then
        printf("For every k <= %a (k in Z), 2k%a+(%a) is a real root with multiplicity %a.\n", k, Pi, 2*arctan(inte[1]), multi);
        # printf("x/2 在 [k%a+(%a)], k <= %a (k \in \Z) 中有 %a 个 %a 重根\n", Pi, arctan(inte[1]), k, num, multi);
    else 
        if num=1 then
            printf("For every k <= %a (k in Z), there is %a real root with multiplicity %a in (2k%a+(%a), 2k%a+(%a)).\n", k, num, multi, Pi, 2*arctan(inte[1]), Pi, 2*arctan(inte[2]));
        else
            printf("For every k <= %a (k in Z), there are %a real roots with multiplicity %a in (2k%a+(%a), 2k%a+(%a)).\n", k, num, multi, Pi, 2*arctan(inte[1]), Pi, 2*arctan(inte[2]));
        end if;  
        # printf("x/2 在 (k%a+(%a), k%a+(%a)), k <= %a (k \in \Z) 中有 %a 个 %a 重根\n", Pi, arctan(inte[1]), Pi, arctan(inte[2]), k, num, multi);
    end if; 
end if;
end proc:

######### proc OneRootOutput
OneRootOutput := proc(num, multi, inte)
# local ;
if inte[1]=inte[2] then
    printf("There is 1 real root with multiplicity %a at %a.\n",  multi, 2*arctan(inte[1]));
    # printf("x/2 在 [%a] 中有 %a 个 %a 重根\n", arctan(inte[1]), num, multi);
else 
    if num=1 then
        printf("There is %a real root with multiplicity %a in (%a, %a).\n", num, multi, 2*arctan(inte[1]), 2*arctan(inte[2]));
    else
        printf("There are %a real roots with multiplicity %a in (%a, %a).\n", num, multi, 2*arctan(inte[1]), 2*arctan(inte[2]));
    end if;
    # printf("x/2 在 (%a, %a) 中有 %a 个 %a 重根\n", arctan(inte[1]), arctan(inte[2]), num, multi);
end if; 
end proc:

######### proc OneRootOutputList
OneRootOutputList := proc(num, multi, lst)
local temp, i;
if numelems(lst)>0 then 
    printf("listnum:%a,%a\n",numelems(lst),multi);
    printf("There is %a real root with multiplicity %a in each open interval of the list [", num, multi);
    # temp :=  Vector[row]();
    # print(lst,numelems(lst));
    for i from 1 to numelems(lst) do
        # temp(i) := [2*temp[i][1],2*temp[i][2]];
        if i<>1 then
            printf(",");
        end if;
        printf("%a", [2*lst[i][1],2*lst[i][2]]);
    end do;
    printf("].\n");
    # printf("There is %a real root with multiplicity %a in each open interval of the list %a.\n", num, multi, lst);
end if;
# printf("x/2 在每个 %a 中有 %a 个 %a 重根\n", lst, num, multi);
end proc:

######### proc Run
run := proc(bclist, m:=-1, n:=-1, eps:=1)
local element, st, i, tm, tn, temp;
tm:=m;tn:=n;
if m<1 then
   tm:=1;
end if;
if n<1 then
   tn:=nops(bclist);
end if;
for i from tm to tn do
    printf("####################\n");
    printf("the i-th: %a\n", i);
    # temp := subs([sin(bclist[i][2])=Sin[x], cos(bclist[i][2])=Cos[x], tan(bclist[i][2])=Tan[x]], bclist[i][1]);
    printf("MTP: %a\n", bclist[i][1]);
    try
        st := time[real]():
        timelimit[real](3600, printf("%a\n",time[real](RootOfMTP(op(bclist[i]), eps))));
    catch:
        printf("Timeout!, %a\n", time[real]()-st);      
    end try; 
end do;
end proc:

######### proc Run
runout := proc(bclist, nolist,eps:=1)
local i,st;
# tm:=m;tn:=n;
# if m<1 then
#    tm:=1;
# end if;
# if n<1 then
#    tn:=nops(bclist);
# end if;
for i in nolist do
    printf("####################\n");
    printf("the i-th: %a\n", i);
    # temp := subs([sin(bclist[i][2])=Sin[x], cos(bclist[i][2])=Cos[x], tan(bclist[i][2])=Tan[x]], bclist[i][1]);
    printf("MTP: %a\n", bclist[i][1]);
    # try
        st := time[real]():
        # RootOfMTP(op(bclist[i]), 1);
        timelimit[real](3600, printf("%a\n",time[real](RootOfMTP(op(bclist[i]), eps))));
    # catch:
    #     print("Timeout!", time[real]()-st);      
    # end try; 
end do;
end proc:

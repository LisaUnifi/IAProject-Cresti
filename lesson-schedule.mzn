%%% DATAs
include "constant-values.dzn";

%%% CORRECTNESS CHECK IN DATAs
constraint assert(d > 0, "Error: Number of days MUST be positive");
constraint assert(n > 0, "Error: Number of rooms MUST be positive");
constraint assert(am > 0, "Error: Number of hours MUST be positive");
constraint assert(pm > 0, "Error: Number of hours MUST be positive");
constraint assert(k > 0, "Error: Number of degree courses MUST be positive");
constraint assert(p > 0, "Error: Number of professors MUST be positive");
constraint assert(t1 > 0, "Error: Minimum number of hours of a lesson in a day MUST be positive");
constraint assert(t2 > 0, "Error: Maximum number of hours of a lesson in a day MUST be positive");

%%% ARRAY DECLARATION
array[1..d] of string: day;
array[1..n] of string: room;
array[1..am] of string: amhour;
array[1..pm] of string: pmhour;
array[1..k] of string: course;
array[1..k] of int: m;
array[1..p] of string: professor;
array[1..p] of int: H;
array[1..p] of int: C;
int: a = sum(i in 1..k)(m[i]); %numero di insegnamenti
array[1..a] of string: lesson;
array[1..a] of int: h;
array[1..p, 1..max(C)] of int: profLes;
array[1..k, 1..max(m)] of int: courseLes;

%%% VAR DECLARATION 
array[1..d, 1..n, 1..am] of var 0..a: amschedule;
array[1..d, 1..n, 1..pm] of var 0..a: pmschedule;

%%% COSTRAINTs 
%The sum of all thw weekly hours must be h[]
constraint forall(z in 1..a)(h[z] = sum(i in 1..d, j in 1..n, w in 1..am)(bool2int(amschedule[i, j, w] = z)) + sum(i in 1..d, j in 1..n, w in 1..pm)(bool2int(pmschedule[i, j, w] = z)));

%in one day, a professor can teach H hours
constraint forall(i in 1..d)(forall(z in 1..p)(H[z] >= sum(j in 1..n, w in 1..am, g in 1..C[z])(bool2int(amschedule[i, j, w] = profLes[z, g])) + sum(j in 1..n, w in 1..pm, g in 1..C[z])(bool2int(pmschedule[i, j, w] = profLes[z, g]))));

%no overlapping of teachings: always possible with this type of structure 

%a professor cannot teach in two different classrooms at the same time
constraint forall(i in 1..d)(forall(z in 1..p)(forall(w in 1..am)(1 >= sum(j in 1..n, g in 1..C[z])(bool2int(amschedule[i, j, w] = profLes[z, g])))));
constraint forall(i in 1..d)(forall(z in 1..p)(forall(w in 1..pm)(1 >= sum(j in 1..n, g in 1..C[z])(bool2int(pmschedule[i, j, w] = profLes[z, g])))));

%no overlapping of lessons in same degree course
constraint forall(i in 1..d)(forall(z in 1..k)(forall(w in 1..am)(1 >= sum(j in 1..n, g in 1..m[z])(bool2int(amschedule[i, j, w] = courseLes[z, g]))))); 
constraint forall(i in 1..d)(forall(z in 1..k)(forall(w in 1..pm)(1 >= sum(j in 1..n, g in 1..m[z])(bool2int(pmschedule[i, j, w] = courseLes[z, g]))))); 

%in one day, the number of hours of a lesson must be between t1 and t2
constraint forall(i in 1..d, j in 1..n)(forall(z in 1..a)(if 0 < sum(w in 1..am)(bool2int(amschedule[i, j, w] = z)) then t2 >= sum(w in 1..am)(bool2int(amschedule[i, j, w] = z)) /\ t1 <= sum(w in 1..am)(bool2int(amschedule[i, j, w] = z)) else true endif /\ if 0 < sum(w in 1..pm)(bool2int(pmschedule[i, j, w] = z)) then t2 >= sum(w in 1..pm)(bool2int(pmschedule[i, j, w] = z)) /\ t1 <= sum(w in 1..pm)(bool2int(pmschedule[i, j, w] = z)) else true endif));

%the same lesson cannot be in different rooms in the same day
constraint forall(i in 1..d)(forall(z in 1..a)(t2 >= sum(j in 1..n, w in 1..am)(bool2int(amschedule[i, j, w] = z)) + sum(j in 1..n, w in 1..pm)(bool2int(pmschedule[i, j, w] = z))));

%hours of the same lesson must be consecutive (length between t1 and t2, included t1 and t2)
constraint forall(i in 1..d, j in 1..n)(forall(z in 1..a)(if 0 < sum(w in 1..t2)(bool2int(amschedule[i, j, w] = z)) then t2 = sum(w in 1..t2)(bool2int(amschedule[i, j, w] = z)) elseif 0 < sum(w in 1..t1)(bool2int(amschedule[i, j, w] = z)) then t1 = sum(w in 1..t1)(bool2int(amschedule[i, j, w] = z)) else true endif));
constraint forall(i in 1..d, j in 1..n)(forall(z in 1..a)(if 0 < sum(w in 1..t2)(bool2int(pmschedule[i, j, w] = z)) then t2 = sum(w in 1..t2)(bool2int(pmschedule[i, j, w] = z)) elseif 0 < sum(w in 1..t1)(bool2int(pmschedule[i, j, w] = z)) then t1 = sum(w in 1..t1)(bool2int(pmschedule[i, j, w] = z)) else true endif));

%choose the type of solver:
solve minimize (sum(i in 1..d, j in 1..n, w in 1..am)(bool2int(amschedule[i, j, w] = 0))); 
%solve satisfy;

%%% OUTPUT
output ["LESSONS SCHEDULE" ++ "\n"];
output ["Day         " ++ " - " ++ "Room  " ++ " - " ++ "Hour   " ++ " - " ++ "Lesson  " ++ "\n"];
output ["\n"];
output [if j = 1 /\ w = 1 then show(day[i]) else "            " endif ++ " - " ++ if w = 1 then show(room[j]) else "      " endif ++ " - " ++ if w <= am then show(amhour[w]) elseif w = am+1 then " 13:00 " elseif w > am+1 then show(pmhour[w-pm-1]) else " " endif ++ " - " ++ if w <= am then if fix(amschedule[i, j, w] != 0) then show(lesson[fix(amschedule[i, j, w])]) else " " endif elseif w > am+1 then if fix(pmschedule[i, j, w-pm-1] != 0) then show(lesson[fix(pmschedule[i, j, w-pm-1])]) else " " endif elseif w = am+1 then " Lunch break " else "        " endif ++ if j = n /\ w = am+pm+1 then "\n" ++ " " ++ "\n" elseif j != n /\ w = am+pm+1 then "\n" ++ "             ----------------------------------" ++ "\n" else "\n" endif | i in 1..d, j in 1..n, w in 1..am+pm+1];






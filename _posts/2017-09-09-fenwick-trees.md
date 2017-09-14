---
layout: post
title: Binary indexed trees/ Fenwick trees 
---

– Range Queries with Point/Range Updates

# A general overview:-
Binary Indexed trees are generally used in problems asking you to update or give the sum of a particular range. Here I am going to deal with two special cases of Fenwick Trees  
1. Range Update with Point Query
2. Range Update with Range Query

The basic form of Binary Indexed Tree is used for Point Update with Range Query, i.e., problems that simplify to  
Given an array A[1..N] , perform the following operations   
1. Add Y to A[X]  
2. Output Sum(A[L..R])  

**Constraints**
* N ~ 100000  
* Q ~ 100000  
* 1<=L<=R<=N  
* 1<=X<=N  
* 1<=Y<=10^9

Where Q is the number of Queries to perform

Knowledge of solving such problems using Fenwick Trees is a prerequisite to this tutorial. You can refer [this](https://www.topcoder.com/community/data-science/data-science-tutorials/binary-indexed-trees/) tutorial on Topcoder to learn basics of Fenwick Trees.

1) Range Update Point Query
We’ll be solving the following problem in this tutorial:-
Given an array A[1..N], all zero initially, perform the following operations:-
1. Add Y to every element in the range A[L..R] 
2. Output A[X]
**Constraints**
* N ~ 100000
* Q ~ 100000
* 1<=L<=R<=N
* 1<=X<=N
* 1<=Y<=10^9  
Where Q is the number of Queries to perform

### Naïve solution
The naïve solution to this problem is very clear
1. We maintain an array of numbers, initialized to zero
2. For every Update query, we iterate over the array from L to R, and add Y to every element
3. For every Output query, we print A[X]
Every output query takes O(1) time and every update query takes O(N) time, so in worst case, the solution will take O(N*Q), which will sadly TLE (unless time limit is a day or two :P )

### A slightly different solution
Instead of updating the whole range why not we just update two indexes. Wait, how! You must be asking, find out below :D  
1. Maintain an array, initialized to zero  
2. For every Update query, add Y to A[L], and subtract Y from A[R+1]  
3. For every Output query, print sum(A[1..X])  
How this works?  
Assume sum(A[X]) gives the correct answer before our update query. Now, when we add Y to A[L], sum(A[X]) for every index>=L will now be increased by Y. But, for index > R, the value must not be increased, therefore we decrease A[R+1] by Y, and now our algorithm gives correct answer for all the indexes again! Since the array was initialized to zero, it will definitely give the correct output for every output query before an update query. Since we just proved that every update maintains the correctness, we have proved that our algorithm is correct by induction. Awesome!

Okay, so now update query is O(1), but now Output query is O(N), so the worst case complexity is 
Still O(Q*N), and our solution will still TLE.
So, why did we even consider this approach? 
Notice something, in this approach update query is essentially updating two indexes (Point Update), and output query is basically sum of first X numbers (Range Query). Which algorithm is fast when it comes to point update range query? Déjà vu?

### Binary Indexed Tree Solution
The solution is basically building our BIT atop the array we defined in the previous approach.
 For every range update query A[L..R], we do two BIT updates, one at index L and the other at index R+1.
 For every point query A[X], we return BIT query at index X. 
Both type of queries runs in O(logN) time, so the overall time complexity is O(Q*log N), which is fast enough to pass time limits. Yay!! :D  
C++ Implementation  
```cpp
template<typename T>class BIT
{
    vector<T> bit;  
    public:  
    BIT(int size=1e5)  
    {  
        bit.assign(size+1,0);  
    }  
    void insert(int start,int end,T val)  
    {  
        for(int i=start;i<bit.size();i+=i&(-i))  
            bit[i]+=val;  
        for(int i=end+1;i<bit.size();i+=i&(-i))  
            bit[i]-=val;  
    }  
    T query(int loc)  
    {  
        T ans=0;  
        for(int i=loc;i>0;i-=i&(-i))  
            ans+=bit[i];  
        return ans;  
    }  
};  
```
[fenwick-trees]: 
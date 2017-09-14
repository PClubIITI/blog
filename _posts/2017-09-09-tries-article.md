---
layout: post
title: "Tries: Pointer free Implementation"
description: "A tutorial to implement tries without the use of pointers"
date: 2017-08-23
author: "Gvs Akhil"
tags: [tech, code, tutorial]
comments: true
share: true
---


In this tutorial, we shall learn how to implement a trie without the use of pointers. The basics and working of a trie should be known beforehand. If not, please read the [prerequisuite](https://threads-iiith.quora.com/Tutorial-on-Trie-and-example-problems).   

We shall deal with a trie containing integers in its binary form.  
The implementation is given below. I shall explain each part further.
```cpp
const int N=1000006,max_edges=2;
int NEW;
typedef struct node{
	int edges[max_edges];
}Trie;
Trie trie[N];
void initialize(int ind){
	for(int i=0;i<max_edges;i++) {
		trie[ind].edges[i]=-1;
	}
}
void pretrie(){
	initialize(0); NEW++;
}
```
# Structure of Trie
```cpp
const int N=1000006,max_edges=2;
int NEW;
typedef struct node{
	int edges[max_edges];
}Trie;
Trie trie[N];
```
In this implementation, each node of the trie is represented by an array which contains the indexes of the other nodes it is connected to by its edges.  
eg. `trie[curr].edges[0]` holds the index of node which is connected to the current node `curr` by the edge which represents `0`.

To create a Trie having `N` nodes, we write `Trie trie[N]` where `trie[i]` represents the i'th node in the trie.      

We also need to maintain a variable which holds the next free index which has not been used yet. Let us name this variable as `NEW`.     
***
# Initializing a Node
```cpp
void initialize(int ind){
	for(int i=0;i<max_edges;i++) {
		trie[ind].edges[i]=-1;
	}
}
void pretrie(){
	initialize(0); NEW++;
}
```
Now, Whenever we create a new node, The edges must not be pointing to any other nodes. Hence we initialize the array with `-1` to indicate the edges do not exist initially.  
Therefore, for every new node, we call `initialize(node_index)` first.    

The `pretrie()` function is only called once at the start of the program to create the root of the tree which is assigned an index of `0`.
# Inserting an Integer
```cpp
const int lastbit=31;
int ch(int x,int i){
	if(x&(1<<i)) return true;
	return false;
}
void insert(int x){
	int ind=0,curr;
	for(int i=lastbit;i>=0;i--){
		curr=ch(x,i);
		if(trie[ind].edges[curr]==-1){
			initialize(NEW);
			trie[ind].edges[curr]=NEW++;
		}
		ind=trie[ind].edges[curr];
	}
}
```
`ch(x,i)` returns the value of the i'th bit in integer `x`. It returns `1` if the bit is set and `0` if it is not. The variable `curr` holds this value.

The condition `if(trie[ind].edges[curr]==-1)` checks whether the current node `ind` does not have an edge corresponding to the value of `curr`.  
If the edge does not exist, a node with index with the value `NEW` is created and is initialized by calling `initialize(NEW);` . Then the line, `trie[ind].edges[curr]=NEW++;` links the newly created node to the current index `ind`.
Also the value of `NEW` is incremented by one since its current value is already taken.  

To move along the edge to the next node, we update the index as `ind=trie[ind].edges[curr];`
***
# Finding Max Xor Value
```cpp
int fmax(int x){
	int ind=0,curr,req;
	for(int i=lastbit;i>=0;i--){
		curr=ch(x,i);
		req=curr^1;
		if(trie[ind].edges[req]!=-1){
			x|=(1<<i);
			ind=trie[ind].edges[req];
		}
		else{
			x&=~(1<<i);
			ind=trie[ind].edges[req^1];
		}
	}
	return x;
}
```
The above function finds the maximum value of `x^y` where `x` is any integer passed to the function and `y` is some integer already present in the trie.  

`ch(x,i)` returns the value of the i'th bit in integer `x`. It returns `1` if the bit is set and `0` if it is not. The variable `curr` holds this value.    

`req` holds the complement of `curr`. It means that req=0 when curr=1 and vice-versa.    

The condition `if(trie[ind].edges[req]!=-1)` checks whether the current node `ind` has an edge corresponding to the value of `req`.  

If the required bit is found, then the i'th bit(from the right) of x is set to `1` by the expression `x|=(1<<i)` . If the required bit is not found, the i'th bit of x is set to `0` by the expression `x&=~(1<<i)` .

`ind=trie[ind].edges[req]` moves `ind` to the next node if the required bit is found.  
`ind=trie[ind].edges[req^1];` moves `ind` to the next node if the required bit is not found.

# Finding Min Xor Value
```cpp
int fmin(int x){
	int ind=0,curr,req;
	for(int i=lastbit;i>=0;i--){
		curr=ch(x,i);
		req=curr;
		if(trie[ind].edges[req]!=-1){
			x&=~(1<<i);		
			ind=trie[ind].edges[req];
		}
		else{
			x|=(1<<i);
			ind=trie[ind].edges[req^1];
		}
	}
	return x;
}
```

The above function finds the minimum value of `x^y` where `x` is any integer passed to the function and `y` is some integer already present in the trie.  

This function is very similar to the fmax function in the previous section but the only chages are-  
* `req=curr` instead of `req=curr^1`
* `x&=~(1<<i)` instead of `x|=(1<<i)` when required bit is found.
* `x|=(1<<i)` instead of `x&=~(1<<i)` when required bit is not found.


# Complete Implementation

```cpp
#include<bits/stdc++.h>
using namespace std;
const int N=1000006,max_edges=2,lastbit=31;
int NEW;
typedef struct node{
	int edges[max_edges];
}Trie;
Trie trie[N];
void initialize(int ind){
	for(int i=0;i<max_edges;i++) {
		trie[ind].edges[i]=-1;
	}
}
void pretrie(){
	initialize(0); NEW++;
}
int ch(int x,int i){
	if(x&(1<<i)) return true;
	return false;
}
void insert(int x){
	int ind=0,curr;
	for(int i=lastbit;i>=0;i--){
		curr=ch(x,i);
		trace4(i,curr,ind,ind);
		if(trie[ind].edges[curr]==-1){
			initialize(NEW);
			trie[ind].edges[curr]=NEW++;
		}
		ind=trie[ind].edges[curr];
	}
}
int fmax(int x){
	int ind=0,curr,req;
	for(int i=lastbit;i>=0;i--){
		curr=ch(x,i);
		req=curr^1;
		if(trie[ind].edges[req]!=-1){
			x|=(1<<i);
			ind=trie[ind].edges[req];
		}
		else{
			x&=~(1<<i);
			ind=trie[ind].edges[req^1];
		}
	}
	return x;
}
int fmin(int x){
	int ind=0,curr,req;
	for(int i=lastbit;i>=0;i--){
		curr=ch(x,i);
		req=curr;
		if(trie[ind].edges[req]!=-1){
			x&=~(1<<i);		
			ind=trie[ind].edges[req];
		}
		else{
			x|=(1<<i);
			ind=trie[ind].edges[req^1];
		}
	}
	return x;
}
int main(){
	pretrie();
	insert(3); 	insert(4); insert(5);
	cout<<fmax(4)<<endl;
	cout<<fmin(4)<<endl;
}
```

# Notes
* When working with 64 bit integers, change `lastbit=31` to `lastbit=63`. Also replace every occurence of `1` with `1LL`.
* This trie can be used with strings by:  
 * Changing `max_edges=2` to `max_edges=26`  
 * Changing `lastbit=31` to `lastbit=str.size()-1` in the insert function.
 * Changing `curr=ch(x,i)` to `curr=str[i]-'a'`
 * Also note that the fmin and fmax functions cannot be using in the case of tries containing strings!

# Design and Analysis of Computational Algorithms 344
## Kostas Bekris	
## Spring 2014

---
---

## Table of Contents

1. [Number Theory](#anchor1)
	1. [Cryptography](#anchor1.1)
	2. [Fermat's Little Theorem](#anchor1.2)
2. [Divide and Conquer](#anchor2)
3. [Greedy Algorithms](#anchor3)
4. [Graphs](#anchor4)
	1. [Depth-First Search](#anchor4.1)
	2. [Shortest Path](#anchor4.2)
		1. [BFS](#anchor4.21)
		2. [Algorithms Table](#anchor4.22)
		3. [Floyd-Warshall](#anchor4.23)
5. [np Problems](#anchor5)

---
---

### 1/31/14

### Recitation

#### TA's:

- Amr Nagruib Nakry <amrbakry@cs.rutgers.edu>
	- Office hours: Tues 12-1 (Hill 206)
	
- Athansios Krontiris <ak979@cs.rutgers.edu>
	- Office hours: Fri 11-12 (BIM-16) 
	
#### Big O and Big $$$\Omega$$$

\\[ \begin{aligned}
&O: f(n) = O(g(n)) \\\
&\exists n_0 > O\;,\;\; c > 0\;\; s,\,t \\\
&\forall n \geq n_0, O \leq f(n) \leq C g(n) \\\
\end{aligned} \\]

---
\\[ \begin{aligned}
&\Omega: f(n) = \Omega(g(n)) \\\
&\exists n_0 > 0\;,\;\; c > 0\;\;\; s,\,t \\\
&\forall n \geq n_0, O \leq Cg(n) \leq f(n) \\\
\end{aligned} \\]

---
##### Small O:
\\[ \begin{aligned}
&o: f(n) = o(g(n)) \\\
&\exists n_0,\;c > 0\;\;\; s,\,t \\\
&\forall n \geq n_0, o \leq f(n) \leq C g(n) \\\
\end{aligned} \\]

---
### Lecture

## [Number Theory](id:anchor1)

### [Cryptography](id:anchor1.1)

- Private cryptography are baaaaadddddd
- Public  cryptography is goooooooddddd
- Think of messages as modulo $$$N$$$
	- Larger messages can be broken into smaller pieces
- What is a good value for $$$N$$$?
- **Property:** Pick any 2 primes $$$p$$$ and $$$q$$$. Let $$$N = p*q$$$ - 
\\[ \begin{aligned}
&\forall e \mid \gcd (e(p-1)(q-1)),\;\; \text{where } e \text{ is a relative prime} \\\
\text{The following are true:} \\\
&\text{1)}\;\; x \to x^e \mod N \;\; \text{ is a bijection}\\\
&\text{let } d = e^{-1} \mod (p-1)(q-1) \\\
\text{Then } \\\
&\forall x \in [0, N-1]:(x^e)^d \equiv x \bmod N
\end{aligned} \\]

##### Proof of Property

\\[ \begin{aligned}
\text{We have to show that} \\\
&(x^e)^d \mod N \equiv X \mod N \\\
&\text{The following are true if } e,\; d \text{ have been selected as specified} \\\
&e * d = 1 \mod (p-1)(q-1) \Rightarrow \\\
&e*d = k(p-1)(q-1) + 1 \\\
\text{Then, check the difference:} \\\
&x^{ed} - x \mod N \equiv x^{k(p-1)(q-1)} - x \mod N
\text{I want to show this O} \\\
\end{aligned}\\]

#### *Fermat's Little Theorem*

\\[ \begin{aligned}
\text{If } p \text{ is prime, then } \forall (1 \leq a \leq p) \\\
1 \mod p \equiv a^{p-1}
\end{aligned} \\]

##### Proof
\\[ \begin{aligned}
&\text{Consider the sets} \\\
&S = \\{1, 2, \cdots , p-1\\}= \\\
&\\{a*1 \bmod p, a * 2 \bmod p, \cdots ,a(p-1) \bmod p \\} \\\
&\text{You will always get a rearrangement of the elements.} \\\
&\text{WHY? } d \* i \bmod p \text{ are all distinct and different from Q}
\end{aligned} \\]

#### Summary of RSA

Bob: 

- Pick 2 large(n-bit) random prime numbers $$$p$$$ and $$$q$$$
- Publish $$$(N,e)$$$ where $$$N = p*q$$$ and $$$e$$$ relative
- Compute private key $$$d=e^{-1} \bmod (p-1)(q-1)$$$

Alice:
- Generate encrypted message $$$y=x^e \bmod N$$$

Bob:
- Decode message $$$x=y^d \bmod N$$$

##### Why is this Secure?

- To break the system, Eve must be able to compute $$$X$$$ given $$$y$$$ and $$$(N, e)$$$
- Try to guess $$$x$$$ so that $$$y=x^e \bmod N$$$
	- Exponential # of guesses as a function of $$$n$$$(# of bits for $$$p, q$$$)
- Alternatively, Eve can try to find values $$$p$$$ and $$$q$$$ so as to compute $$$d=e^{-1} \bmod (p-1)(q-1)$$$
- What do we know about $$$p$$$ and $$$q$$$? 
	- They are primes and $$$p*q=N$$$
- But this is the factoring problem
	- believed to be hard and intractable
- What are the operations of RSA and what is the running time?
	\\[ \begin{aligned}
	&\Rightarrow \text{Modular exponentiation } \\\
	&y=e^x \bmod N\over x=y^d \bmod N \\\
	&\Rightarrow \text{Select } e \text{ so relative prime to } (p-1)(q-1) \\\
	\end{aligned} \\]

#### Modular Exponentiation

$$x^y \bmod N$$
How big can $$$x^y$$$ get? e.g. for 20-bit numbers
$$(2^{19})^{13} = 10\text{ mil. bits long}$$
We need to perform all intermediate computations $$$\bmod\; N$$$ $$x \bmod N \to x^2 \bmod N \to x^3 \bmod N$$
If $$$y$$$ is 500 bits long then I have to do the multiplication $$$2^{500}$$$ times.

Idea: square every intermediate result
$$x \bmod N \to x^2 \bmod N \to x^4 \bmod N \to x^8 \bmod N \to x^{16} \bmod N$$
Now there are $$$n^3$$$ multiplications

$$x^{25_{10}} = x^{11001_2} = x^{10000} * x^{010000} * x^{00001} = x^{16} * x^8 * x^1$$

Sample function:

		function modexp(x,y,N)
		if (y = 0) return 1
		Z = modexp(x, floor(y/2), N)
		if (y is even)
			return z^2 mod N
		else
			return (x * z^2 mod N)

---
### 2/7/14

#### Greatest Common Divisor

\\[ \begin{align}
1035 = 33 * 5 * 23 \\\
759 = 3 * 11 * 23 \\\
\end{align} \\]

##### Euclid's Observation

$$\gcd(x,y) = \gcd(x \bmod y, y)$$
Let's show that: $$$\gcd(x,y) = \gcd(x-y, y)$$$
$$\gcd(x,y) \leq \gcd(x,x-y)$$

$$$g$$$ divides both $$$x$$$ and $$$y$$$

	function Euclid(a,b) {
		if b = 0
			return a;
		return Euclid(b, a mod b);
		}
$$$\text{Euclid} = O(n^2)$$$
\\[ \begin{aligned}
\text{if}\;\; a \geq b \text{ then } a \bmod b < \frac{a}{2}
\end{aligned} \\]

##### Lemma

If $$$d$$$ divides both $$$a$$$ and $$$b$$$ and we can write $$$d=ax+by$$$ for $$$x,y$$$ integers 

then $$$d=gcd(x,y)$$$

Since $$$d$$$ divides $$$a$$$ and $$$b$$$,
$$a \bmod d = b\bmod d$$

[insert shit here]

	function extended Euclid(a,b)
		if b = 0
			return x = 1, y = 0, d = a;
			(x',y',d') = extended Euclid(b a mod b);
			return(y', x' - ceil(a/b) * y', d);
			
#### Multiplicative Inverse modulo N

$$$x$$$ is a m.i.m.N. of $$$a$$$ if $$ax \equiv 1\bmod N$$

(In RSA $$$de\equiv 1\bmod (p-1)(q-1)$$$)

Such an inverse does not always exist	

When $$$\gcd(a,n) = 1$$$ then Extended Euclid algorithm gives an expression

Ex: Find the inverse of 11 modulo 25

\\[\begin{aligned}
\gcd(11,25) &= \gcd(25,11) \\\
&=\gcd(25,11) \\\
&=\gcd(11,3) \\\
&=\gcd(3,2) \\\
&=\gcd(2,1) \\\
&=\gcd(1,0) \\\
\end{aligned} \\]

#### Modular Division Theorem

\\[\begin{aligned}
&\forall a\in [1,\dotsc, N] \\\
&a \text{ will havea  multiplicative inverse modulo }N \\\
&\text{ if it is a relative prime to } N \\\
\end{aligned} \\]

#### Primality Test (Test of Prime-ness)

Remember Fermat's Little Theorem:

If $$$p$$$ is prime, then $$$1 \leq a < p$$$ $$A^{p-1} \equiv 1\bmod p$$

Pick an value $$$a$$$. If it doesn't not satisfies the *Primality Test*, $$$p$$$ is not prime.
- We hope that if we call this test multiple times for a non-prime $$$p$$$ that it will fail quickly.

function Primality(N):

pick positive integer $$$a \in [1, N-1]$$$ at random

if $$$(a^{N-1}\equiv 1\bmod N)$$$ return SUCCESS

else return FAILURE

- **Carmichael numbers:** Not prime but Fermat's test succeeds.
	- Ignore these numbers for now (they are rare)
- Thus for a prime number test will always succeed
- For a non-prime it will fail with a certain probability

---
### 2/14/14

### Recitation

- How do you prove $$$a\equiv a\pmod n$$$
	- Show that $$$n\;|\;a-a\to n\;|\;0$$$
- In general, $$$a\equiv b\pmod n \iff n\;|\;a-b$$$

#### Substitution Rule:
\\[\begin{aligned}
&x\equiv y\bmod n,\; x'\equiv y'\bmod n \\\
\implies &x + x'\equiv y + y'\bmod n \\\
\implies &x * x'\equiv y * y'\bmod n \\\
\end{aligned} \\]

- Let $$$n$$$ be a nonnegative integer. Prove $$$n\equiv n\bmod 10$$$
\\[\begin{aligned}
	ed&\equiv 1\pmod{(p-1)(q-1)} \\\
	(m^e)^d&\equiv m\bmod{pq} \\\
	ed &= k(p-1)(q-1) + 1 \\\
	m^{ed} &= m^{1+k(p-1)(q-1)}\equiv m\bmod pq \\\
	p-q &=10\,,\;1+k(p-1)(q-1) = 5 \\\
	\text{for }\; p&=5,\;q=2
\end{aligned}\\]
 
 - for $$$k\in \mathbb{Z}, k$$$ is a self-inverse iff
 	\\[\begin{aligned}
 	k*k\equiv1&\bmod \;p\; (p\text{ is prime}) \\\
 	p\;|\;k^2-1&\iff p\;|\;(k-1)(p-1) \\\
 	p\;|\; k-1 &\text{ or } p\;|\;k+1 \\\
 	k-1=np &\text{ or }k+1=np \\\
 	k=np\pm1&\implies k\equiv\pm1\bmod p \\\
 	\end{aligned} \\]

---
### Lecture

#### Divide & Conquer

- Break your problem into smaller instances
- Recursively solver smaller subproblems
- Combine these answers
- Before for multiplication: $$x*y=2x\*\Big\lfloor{y\over2}\Big\rfloor$$ if $$$y$$$ is even, $$x+2x\*\Big\lfloor{y\over2}\Big\rfloor$$ if $$$y$$$ is odd.
- Another idea for multiplication:
	$$x: 10101\,|\,00100\quad x=2^{n/2}*x_L+x_R$$
	$$y: \quad y_L\quad\quad y_R \quad\quad y=2^{n/2}\*y_L + y_R$$
- In the above representation, we have
	- additions (linear cost)
	- multiplication with powers of 2 (linear cost) (left shifts)
	- four multiplications between $$$n/2$$$-bit numbers
- We can define a recursive relations:$$T(n)=4T\left({n\over2} + O(n)\right)$$
- Gauss' observation: Rework the above expression so as to make use of only 3 $$$n\over2$$$ size multiplications. $$x_Ly_R + X_Ry_L = (x_L + x_R)(y_L + y_r) - x_Ly_L - x_Ry_R$$
$$x\*y=2^nx_Ly_L+2^{n\over2}(x_Ly_R+x_Ry_L) = x_Ry_R$$
$$x\*y=2^nx_Ly_L+2^{n\over2}(x_Ly_R+x_Ry_L) = x_Ry_R$$
$$T(n)=3T\left({n\over2} + O(n)\right)$$
- Make a tree of height $$$\lg n$$$
- We are solving mult. w a d&c approach
- By decreasing # of recursive calls we managed to get a running time

#### Master Theorem

- If you have a recursive case the function of the form $$$T(n) = a*T\left\lceil{n\over b}\right\rceil + O(n^d)$$$ then: $$$T(n) = O(n^d), O(n^d\log n), O(n^{\log_b a})$$$ for $$$d >, =, < \log_b a$$$
- Assume that $$$n$$$ is a power of $$$b$$$ for convenience
- The size of the problem decreases by $$$b$$$ at every level
- We need $$$\log_b n$$$ levels to stop the recursion.
- At level $$$k$$$ we have $$$a^k$$$ subproblems of size $$${n\over b} k$$$
- Work at level k: $$a^k * O\left({n\over b^k}^d\right) = O\left(n^d\right)*\left({a\over b^d}^k\right)$$
- **3 cases:**
	1. If $$${a\over b^d} < 1$$$: series is decreasing. Dominating term is the first one
		- Running time: $$$O(n^d)$$$
	2. If $$${a\over b^d} > 1(\implies d < \log_b a)$$$: series is increasing. Dominating term is the last one
		- Running time: $$$O(n^{log_b a})$$$
	3. If $$${a\over b^d} = 1 (\implies d=\log_b a)$$$ then all terms are equivalent to $$$O(n^d)=O(n^{log_b a})$$$
		- Overall cost: $$$O(n^d\log_b n)$$$
- The overall cost is also going to be some eq that Bekris fucking covered up
	- t(-.- t)
	
##### Example: Binary Search

\\[\begin{aligned}
T(n) = 1 * T\big({n\over 2}\big) + O(1) \\\
a = 1, b = 2, d = 0
\end{aligned}\\]

#### Sorting Problem

- A sequence of elements $$$(a_1,\dotsc,a_n)$$$ output a permutation $$$(a_1',\dotsc,a_n')$$$ so that $$$\forall i\,\exists j$$$ such that $$$a_j' = a_i$$$ and $$$a_1'\leq a_2'\leq \dotso\leq a_n'$$$
- We will review 2 families of sorting algorithms:
	- Comparison sorts:
		- Merge sort
		- Heap sort
		- Quick sort
		- Insertion sort
	- Non-comparison sorts:
		- Count sort
		- Radix sort

- **Merge Sort**
	- Split the list into two halves. Recursively sort each half and then merge them.
	- Cost of merging two sorted $$$n\over2$$$ lists is $$$O(n)$$$	\\[\begin{aligned}
	T(n) = 2 * T({n\over2}) + O(1) \\\
	a = 2, b = 2, d = 1
	\end{aligned}\\]
	
---
### 2/26/14

### [Greedy Algorithms](id:anchor3)

- For 2 pennies and 3 dimes The greedy algorithm will never return a solution that surpasses these bounds for each coin type and first maximizes the # of coins of the highest value, minimizing their number.
- **Application:** *Compressing Data*
- Assume you have a signal and you are digitizing it
- Each measurement can be represented in an alphabet of 4 values, A, B, C, D
- What is the most economical way to transmit this signal?
- Desired property: Prefix-free code where no codeword can be a prefix of another codeword
- Prefix-free encodings can be represented by a full binary tree (Nodes have 0 or 2 children)
	- Symbols assigned to leaves
	- codeword is generated by a path from the root to a leaf interpreting left as 0 and right as 1
- How do we find the optimal coding tree?
- Consider the cost of the tree: $$\mathrm{Cost} = \sum_{i=1}^n f_i*(\text{depth of ith symbol on tree (equal to # of bits))}$$ where $$$f_i$$$ is the frequency of the symbol.
- We can also define frequencies for internal nodes as the sum of frequencies for the children.
- Each time we move down the tree, we have to use an extra bit, which will increase the cost by the frequency of all the leaves. $$\mathrm{Cost} = \sum_{j=1}^k f_j',$$ $$$f'j$$$ is the frequency of the internal/leaf nodes
- **Approach:**
	1. Find the two symbols with the lowest frequency w/o loss of generality, $$$l_x$$$ and $$$l_y$$$
	2. Make them children of a new node
	3. Remove the frequences $$$f_x$$$ and $$$f_y$$$ from consideration and replace them with a frequency $$$(f_x+f_y)$$$
	
##### Huffman Encoding $$$\;f[1...n]$$$

\\[\begin{aligned}
\mathcal H \gets \text{priority queue ordered by }f \\\
\mathrm{for}\; i=1\to n \\\
\mathcal H, \text{ insert } (f[i]) \\\
k = n + 1\to 2n+1 \\\
i = \mathcal H.\mathrm{popMin} \\\
j = \mathcal H.\mathrm{popMin} \\\
\text{create node } m \text{ with children } i \text{ and } j \\\
f[m] = f[i] + f[j] \\\
\end{aligned}\\]

##### Correctness of Huffman Encoding

Lemma $$$G$$$: an alphabet of symbols with frequencies $$$f[c], c\in G, x, y: $$$ lowest frequency symbols.
- Then there exists an optimum prefix-free code for $$$G$$$, where $$$x$$$ and $$$y$$$ are at the same length and differ only in the last bit
- Let $$$a$$$ and $$$b$$$ be 2 characters that are sibling leaves of maximum depth of encoding tree. Assume w.l.o.g. $$$f[x]\leq f[a]$$$ and $$$f[y]\leq f[b]$$$.
\\[\begin{aligned}
C(T) - C(T') &= \sum_{c\in G}f[c]\*d_T[c] - \sum\_{c\in G}f[c]\*d\_{T'}[c] \\\
&= f\[x]\*f\_T(x) + f(a)\*d\_T(a) - f(x)d\_{T'}(x) - f(a)d\_{T'}(a) \\\
&= f\[x]\*f\_T(x) + f(a)\*d\_T(a) - f(x)d\_{T}(x) - f(a)d\_{T}(a) \\\
&= f\[x](d\_T(x) - d\_T(a)) - f(a)(d\_T(a) - d\_T(x)) \\\
&= (d\_T(a) - d\_T(x))(f[a] - f[x]) \implies C(T) - C(T') \geq 0 \\\
&\implies C(T')\leq C(T) \\\
\end{aligned}\\]

- **Lemma:** $$$C'$$$ alphabet similar to $$$C$$$ with $$$x\;y$$$ replaced by $$$z$$$ with frequency $$$f(x)+f(y)$$$.
- $$$T'$$$ optimal prefix code for $$$C'$$$
- Tree $$$T$$$ is obtained from $$$T'$$$ by replacing $$$z$$$ with an internal node that has $$$x$$$ and $$$y$$$ as children.
- $$$T$$$ is optimal for $$$C$$$. $$C(T') = C(T) - f[x] - f[a]$$
- Assume $$$T$$$ is not optimal for $$$C$$$.
- There is then $$$T''$$$ better cost
- Let $$$T'''$$$ is generated from $$$T''$$$ with $$$x$$$ and $$$y$$$ replaced by 2 $$$\quad f[z] = f[x] + f[y]$$$

---
### 3/6/14

### Dynamic Processing

Ex: Matrix Multiplication

- For each element $$$m$$$ the resulting $$$m x n$$$ matrix you have to perform $$$O(n)$$$ multiplications
	- So overal $$$O(mpn)$$$
- What if you have a large number of marices?

When does dynamic programming apply?

- Properties for your problems:
	- Optimal substructure
	optimal solutions to a problem contain optimal solutions to subproblems
	- overlapping subproblems
- Differs from greedy algorithms b/c G.A. are top-down

Ex: Longest Increasing Subsequence

- Given a sequence of numbers $$a_1,\dotsc,a_n$$ There is a subsequence subset of numbers taken in order $$a_{i1}, a\_{i2},\dotsc, a\_{ik},\quad i_1\leq i_2\leq\dotso \leq i_k$$

What are the subproblems?

- Smaller sequences
- Consider that you know the longest increasing subsequence for all subsequences

\\[\begin{aligned}
a_1 \\\
a_1a_2 \\\
\vdots \\\
a_1a_2\dots a_{n-1} \\\
\quad a\_{n-1} > a_n \\\
\end{aligned}\\]

- Denote as $$$L(j)$$$ the length of the longest increasing subsequence that considers the first $$$j$$$ digits and the last element. 
- $$L(n )= 1 + \mathrm{max}_{j\,\in \,[1,n-1]}\;\{L(j), \forall j: O(n) > O(j)\}$$
- $$LIS(1\dotsc n)$$

- Edit distance
	- Cost of the possible alignment (adding, removing, or substituting a character)

- Let's say we have strings: $$x[1\dotsc i]$$ $$y[1\dotsc j]$$
- What happens with the last characters $$$x[i]$$$ and $$$y[j]$$$?
	- The world will never know
	
---
### 3/12/14

### Longest Common Subsequence

	S-NOWY
	SUNN-Y
	------
	010110
	
##### Subproblems

- $$$x[1\dots i]$$$
- $$$y[1\dots j]$$$
- How can the last two characters be potentially aligned if we know the alignment between

\\[\begin{align}
x[1\dots i-1] \\\
y[1\dots j-1] \\\
\end{align}\\]

- Depends on subproblem
- Cost is 0 if $$$x[i] = y[j]$$$ or 1 if they are different
- if there is a gap, edit distance increases by 1

\\[\begin{aligned}
E[i,j] = min\,\\{ \\\
&E[i-1,j-1] + \mathrm{diff}(x[i],y[j]) \\\
&E[i-1, j] + 1 \\\
&E[i, j-1] + 1 \\\
\\} \\\
\end{aligned}\\]

##### Knapsack Problem

- You can carry $$$W$$$ pounds total
- $$$n$$$ items to pick from

\\[\begin{aligned}
\text{weight } w_1,\dotsc , w_n \\\
\text{value } v_1,\dotsc , v_n \\\
\\end{aligned}\\]

What is the most valuable collection of items we can carry?

Two versions:

- Repetition of items (opt. sol item 1, item 4, item 4)
- Or no repetition

###### Without Repetition

- Subproblems: smaller weight threshold $$$W$$$
- $$$K(w)$$$: maximum value you can get for weight $$$w$$$
- $$$K(2) = \mathrm{max}\\{k(w-w_1 + v_i\\}$$$
- *Algorithm:*

		K(0) = 0
		for w=1 to W
			k(w) = max{k(w - w_1 + v_i, w_i <= w}
		return k(w)
	
- For each cell I may have to consider up to $$$n$$$ items
- \# cells: W
- $$$O(nW)$$$
	- This could be exponential number of $$$n$$$, depending on size of $$$W$$$
	
For **Knapsack** w/o repetition
	- Subproblems: we also have to keep track of the objects already in the solution
	- $$$K(w,j)$$$: maximum value for napsack with weight $$$w$$$ while picking only among the first $$$j$$$ items

---
### 3/26/14
## [Graphs](id:anchor4)

- **Connectivity Notion for directed graphs**
	- Nodes $$$u$$$ and $$$v$$$ of a directed graph are connected if there is a path from $$$u$$$ to $$$v$$$ and vice versa.
	- This relation partitions directed graphs into disjoint sets of strongly connected components
- **Property:** Every directed graph is a DAG of its strongly conected components
	- Remember that the *explore* function of DFS returns the set of nodes that are reachable from the input vertex
- If we select a node in a SCC that is a sink in the meta-graph, then we will retrieve exactly this component
	- How can we know that we are on a sink SCC?
	- How do we continue after the first sink has been discovered?

### [Depth-First Search (DFS)](id:anchor4.1)

- **Property of DFS:** The vertex with the highest post order is a source vertex
- If we reverse a graph $$$G$$$ into graph $$$G^R$$$, then source(sink) nodes in $$$G$$$ become sink(source) nodes in $$$G^R$$$
- **Property:** If $$$C$$$ and $$$C'$$$ are SCG's and $$$\existsE$$$ from a node in $$$C$$$ to a node in $$$C'$$$, then the highest post-order in $$$C$$$ is bigger than the highest post-order in $$$C'$$$
- But we know how to find sources vertices using DFS on $$$G^R$$$, so we can find sinks on $$$G$$$
- Overall:
	1. Run DFS on $$$G^R$$$ to provide an ordering of vertices based on highest post-order in $$$G^R$$$
	2. Based on this order, call the explore function and discover the vertices belonging to a sink SCC
	3. Remove all these vertices
		- Repeat from 2.

- DFS is a *Linear-Cost Algorithm*

### [Shortest Path](id:anchor4.2)

- DFS - discovers all vertices reachable from an input vertex and returms path for them
- But this does not find the shortest path from any input vertex.
- *Breadth-First Search* will actually return shortest paths in terms of the number of edges
- **Traversal:** Search the graph in order of depth from the input vertex

#### [Breadth-First Search](id:anchor4.21)

1. Maintain a FIFO queue
2. For every node dequeued, visit all the children of that node if it has not been already visited

		public void bfs(Vertex u) {
			u.visit(null);
			u.visited = true;
			q = new Queue();
			q.enqueue(u);
			while (!q.isEmpty()) {
				v = q.dequeue;
				for (each vertex w such that (v,w) is an edge in E) {
					if (!w.visited) {
						w.visit(v);
						q.enqueue(w);
						}
					}
				}
			
		public class Vertex {
			protected Vertex parent;
			protected int depth;
					
			public void visit(Vertex origin) {
				this.parent = origin;
				if (origin == null) {
					this.depth = 0;
					} else {
					this.depth = origin.depth + 1;
					}
					w.visited = true;
				}
			}
				
#### Inductive Argument for correctness

There is a moment at which:

1. All nodes at distance $$$d$$$ from the input vertex have the correct distance computed
2. All the other nodes have their distance set to $$$\infty$$$
3. The queue contains exactly the nodes at distance $$$d$$$ - their unvisited neighbors will get distance $$$d+1$$$

**Running Time:** - $$$O(|V| + |E|)$$$

*BFS* does not take into account weights on the edges

**Problem:** Given a graph $$$G(V, E)$$$ and a weight function $$$w: E\to\mathbb R$$$, where the weight of a path is given as $$w(p) = w({u_0, u_1,\dotsc,u_n}) = \sum\_{i=0}^{n-1} w(u_i, u\_{wi})$$
- Shortest distance between $$$u$$$ and $$$v$$$

\\[\begin{align}
S(u,v) &= \mathrm{min}{w(p):u\to v}\text{ if } \exists P \\\
&= \infty, \text{ otherwise} \\\
\end{align}\\]

##### Versions of shortest path problems

- Single-source shortest paths given $$$G(V,E)$$$, find the shortest path from 

**Key Property (Optimal Substructure):** Given a weighted, directed graph $$$G(V,E)$$$ with weight function $$$w:E\to\mathbb R$$$, let $$$p = <u_1,\dotsc,u_k>$$$ be a shortest path from $$$u_1$$$ to $$$u_k$$$.

Then $$\forall i,j: 1\leq i\leq j\leq k$$
Then the subpath $$$P\_{ij} = <u_i, u\_{i+1},\dotsc, u\_{j-1}, u_j>$$$
is the shortest path between $$$u_i$$$ and $$$u_j$$$ if $$$\exists|P'\_{ij} < |P{_ij}|$$$ 

Then replace it in $$$p$$$ to get a shorter path $$$p$$$ from $$$u_1\to u_k$$$

##### Problems

- What happens with negative weight edges?
- They may create negative weight cycles
	- In this case the shortest path is not well-defined
	$$\delta(s,t) = -\infty$$
- Assume no negative weight cycles
- Positive weight cycles cannot be part of shortest paths
	- (always be removed to give something shorter )
- Zero weight cycles give rise to an infinite number of shortest paths - select the one without the cycle

---
### 4/4/14

#### [Shortest Paths Table](id:anchor4.22)

Problem | Approach | Running Time
:-------|:---------|:------------
No edge weights | BFS (FIFO) | $$$O(|V|+|E|)$$$
Non-negative edge weights | Djikstra's (Priority Queue | $$$O(|V|\log|V| + |E|)\over O(|E|\log|V|)$$$
Negative edge weights | Bellman-Ford | $$$O(|V||E|)$$$

##### Dynamic Programming Approach for ADSP

- **Subproblem:** Shortest paths for all pairs of nodes that go through a subset of the nodes

#### [Floyd-Warshall](id:anchor4.23)

	for i=1 to |V|
		for j = 1 to |V|
			dist(i,j,0) = infinity
		for (i,j) in E
			dist(i,j,0) = w(i,j)
		for k = 1 to |V|
			for i = 1 to |V|
				for j = 1 to |V|
					dist(i,j,k) = min{dist(i,k,k-1) + dist(k,j,k-1), dist(k,j,k-1),dist(i,j,k-1)}
					
Running Time: $$$O(|V|^3)$$$
Space Complexity: $$$O(|V|^2)$$$

- Although Djikstra's algorithm is more efficient than Floyd-Warshall, it requires positive edge weights
- Can we transform the input graph to a new graph that always has positive edge weights and reports the same shortest paths?
- The new weights must satisfy the following requirements:
	1. $$$\forall u,v \in \mathit B$$$: if $$$p$$$ is the shortest path from $$$u\to v$$$ given $$$w$$$, then $$$p$$$ should stilll be the shortest path from $$$u\to v$$$ given $$$w'$$$
	2. $$$w'(u,v)\geq 0$$$
	
Idea: assume a value $$$h(v)\;\forall v\in \mathit V$$$
and define $$$w'(u,v) = w(u,v) + h(u)-h(v)$$$

- *Lemma:* for the $$$w'$$$ weights the first requirement is satisfied

$$w'(p) = \sum\_{i=0}^{n-1}w'(u_i,u\_{i+1}) = \sum\_{i=0}^{n-1} w(u_i,u\_{i+1} + h(u_i)-h(u+i)$$

##### Construction so as to achieve $$$w'(u,v)\geq 0$$$

- Augment the graph: $$$G' = \\{Vu\\{s\\}, Eu\\{s,v\\} \forall v\in V\\}$$$
- No new shortest path exists in $$$G$$$ that did not exist in $$$G$$$ beyond paths from $$$s$$$ to $$$v$$$ ($$$s$$$ has no incoming edges)
	- Define $$$h(v)=\delta(s,v)$$$, where $$$\delta(s,v)$$$ is the length of the shortest path
	
---
### 4/25/14

### [$$$np$$$ problems](id:anchor5)

- To prove: 
\begin{align}
p&\subseteq np \\\
np&\subseteq p \\\
\end{align}

- if we can prove $$$np = p$$$, it means that computers can solve all mathematical problems
- *Problem:* TSP: Given $$$n$$$ vertices, and all $$$n(n-1)\over 2$$$ distances between the vertices and a budget $$$b$$$. Find a cycle that passes through all the vertices once and the total distance $$$\leq b$$$. If no such cycle exists, return "Impossible".
	- Given a graph $$$G=(V,E)$$$
	- Construct a new graph $$$G=(V,E')$$$
	\begin{align}
	E'=\big\\{(u,v)\;|\;U,v\in V \;&\text{if }(u,v)\in E, (u,v)=1\big\\} \\\
	\\{&\text{else }(u,v)=1 + \infty\\} \\\
	\end{align}

- if $$$p\neq np$$$
- What do you do when you have a difficult problem?
- Figure out whether it reduces to an $$$np$$$-complete challenge
- Identify whether your input is of limited and size and implies an easier instance than the general case
- Alternatively, follow a search approach
	- it might take exponential time in the worst case
	- But it will iuse primitives that will speed up the solution for most inputs
	- Backtracking search
**Approximation algorithms**
	- Get within a known bound of the optimum solution
- **Heuristic solutions**
	- No guarantees
	- Based on intuition they aim to provide quick solutions
- **Intelligent Exchausive Search**
	- search-based problems: Backtracking
	- Observation: that we can often reject a solution by looking at just a subset of an algorithm
	
#### 	An Intelligent Exhaustive Search

- Optimization variant: Branch-and-bound
- *Observation:* a partial solution may indicate a cost that is higher thana cost of a com[plete solution already discovered.
- *Example:* Consider an optimization version of TSP graph $$$G(V,E)$$$ with edge weights $$$D_e > 0$$$.
	- Partial solution set: $$$[a,s,b]$$$

#### Approximation Algorithms

- Instance $$$I\to OPT(I)\text\from{ <- utility/cost of soln}$$$
- minimization:
	- Suppose Algorithm A returns cost A(+) for instance I
	- Then the **approx. ratio** of A is defined to be $$\alpha_A =\mathrm{max} {A(I)\over OPT(I)}$$
	(worst-case performance of the algorithm)
	
	For maximization problems we consider the reciprocal ratio.
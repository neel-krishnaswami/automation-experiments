# Formatting notes 

The layout of the thesis is a bit rough. 

- Ensure there is a page break so that every chapter starts on a new page. 

- Make the chapter, section, and subsection boldface to create more visual
  distinction between the content and the structure. 

# Chapter 1. 

## Section 1.1 Motivation 

- On page 5, SDQL is introduced without explanation. 

- You need to explain what betweenness centrality is (informally), and why it is 
  relevant to the problem. 

Advice: 

1. Keep the opening paragraph 
2. Explain the problem of working out "who the most important actor is", and
   why betweenneess centrality is a good formalization of this idea. 
3. Lay out a typical implementation strategy:
   - Compute a join in SQL to compute the costar relation. 
   - Compute all-pairs shortest paths on the costar graph using Neo4J
   - Use NumPy on this relation to compute the fraction of all-pairs 
	 shortest paths passing through each node. 
4. Introduce SDQL as a unifying language that can uniformly handle 
   relational, graph, and linear algebra computations. 
   
The stuff you did should be moved into a new subsection
"Contributions" at the end of chapter 1. Specifically, move the stuff
starting "Thus, we are naturally motivated for the following research
questions" into its own subsection. 
   
## Sections 1.2 and 1.3 

Swap the order of these two: SDQL as a language doesn't make sense until 
you explain *why* it is reasonable to look for a unifying abstraction 
at all. 

### For the intuition section, explain that: 

- Relations are boolean-valued matrices

- Data science works with real-valued matrices

The common structure needed by matrix operations (such as
multiplication) is addition and multiplication, which means that
semirings form the common abstraction for both relations and
real-valued matrices.

Then, explain that graph algorithms can be formulated in terms of
adjacency matrices, and many transitive closure algorithms correspond
to lifting Kleene closure from elements to square matrices. Sketch
the Kleene structure of the Booleans to illustrate. Add a forward 
reference to section 2.6 for details. 

### For the background on SDQL section 

Give examples of small SDQL programs, and move the main informal
design to the end of chapter 2. 

## Section 1.4 Prior work

This is very good, no change needed. 

## Section 1.5 Background on Lean4 

This is a stub that you can delete. Fold it into your
new contributions subsection. 

# Chapter 2 

Add a page break between chapters. I would add a section about 
SDQL, in more detail than in chapter 1, but not in full detail 


## Section 2.1 

Tighten the opening. Say what you did and why you did it; don't
explain what you didn't do (i.e., everything about Waterfall can
be deleted). 

### Subsection 2.1.2

Too many single-sentence paragraphs in this subsection. Consolidate. 

## Section 2.2 

Good 

## Section 2.3

The content is good, but you can consolidate almost all of the single-sentence paragraphs. 

## Section 2.4 

Again, too many single-sentence paragraphs. Consolidate. 

## Section 2.5 

This is generally excellent, except for a small issue with section 2.5.3. 

### Subsection 2.5.3 Tradeoffs of the compilation target

The justification for compiling to Rust is pretty weak. You might want to 
suggest instead that because Rust is strongly-typed and safe, it makes catching
code generation bugs easier than if you generated C or C++. 

Also, explain what the issues with the borrow checker actually are! 

## Section 2.6 

Explain what a semiring is before moving on to Kleene algebras. 

## [TO ADD] Section 2.7 Introduction to SDQL

Give a slightly fuller description of SDQL here, including what its 
types and typing judgement look like. This will set you up for talking
about the Lean datastructures representing it in Chapter 3. 


# Chapter 3. 

Again, ensure that the chapter starts on its own page. The main issue
in this chapter is that the architecture of your implementation is
unclear. The reason it is not clear is because you do not explain what
the data structures you use are. (As Fred Brooks said long ago, "Show
me your tables, and I won't usually need your flowchart; it'll be
obvious".)

## 3.1 Introduction to Lean 

This is a good example of how the lack of clarity about the data
structures hurts you. You move straight from vectors to typechecking,
and never even explain that `.int` refers to an SDQL int type!

Change the title of this section to "Core data structures in Lean" 
or something, and make the emphasis of the chapter explaining: 

1. SDQL types, represented as Lean types
2. SDQL contexts, represented in Lean 
   - This is a good point to briefly remind the reader what
	 de Bruijn indices are. 
3. The indexed type representing well-typed SDQL terms. 

You don't need to show all the constructors, but show one or two
simple ones, and one or two more complex ones, so the reader can
understand how you are represent SDQL typing information in Lean
types.

Also, one or two signatures of functions which maintain interesting
invariants would be good to give here, such as the signature of the 
typechecker.

## 3.2 Compilation Pipeline 

This section is extremely hard to read: it is very choppy and
fragmented. This is partly because many "subsections" are just single
sentences like "The high-level compilation pipeline is describe in
Figure 2." There is no content here that requires a subsection: the
position of the figure is basically a parenthetical comment.

Another reason is that your description follows the flow of the
codebase too closely. You need to start with the *most important*
implementation choices, and explain those first. Once a reader
understands those, then the rest of the compiler will be obvious. 

Merge many of these subsection (especially 3.2.1 -- 3.2.2.2) into a
single unit. Then, go through this and explain the things you did not
explain:

- You never explain what a syntax macro is, or what you are using them
  for: a reader might not even realize you're not using a separate 
  parser! You hint at a payoff in 3.2.3, but a reader who hasn't realized
  you extended Lean syntax will not get it. 

- You never explain what PHOAS is. 

- You never explain *why* loads are replaced with free variables. 

- You never explain what evidence is, what the different kinds are, 
  and why you have to synthesize it. 


Turn 3.2.4 into its own section, and explain more clearly that the
"unsafe" Lean violates the logical consistency of Lean as a proof
assistant, but that all of the code you wrote is still completely
type-correct in the conventional sense, and. 

## Section 3.3 

Table 7 is redundant with the table in chapter 2. 

## Section 3.4 

The notation End(V) ≃ M_{n(k)} is not defined anywhere. 

## Section 3.5

Good 

## Section 3.6

Again, this presupposes understanding that syntax macros extend the Lean elaborator, 
which you never explain! 

## Section 3.7 

Eliminate the subsections, but otherwise good. 

## Section 3.8 

Ok, but say whether the performence improvements paid off or not! 

# Chapter 4 

## Section 4.1

## Section 4.2 

> "I thought that using dependent types would lead to a shorter
> implementation, but it doesn't.  That's interesting."

It is interesting! That's why you should actually say something about how the implementations
differ! Why is the rewrite module 5.5x bigger in Lean? Why is your typechecker so much bigger? What
choices does the Scala implementation make, and could you do something similar? 

## Section 4.3 

This is good, but merge your lonely sentences into coherent paragraphs. 

## Section 4.4

Excellent performance analysis. 

## Section 4.5 

You should explain *why* your implementation is slower, if you can. (I assume it is 
mostly copying too much.) 

## Section 4.6-7

Good! 

## Section 4.8 

Expand out "CDNs" to "Cognitive Dimensions of Notation". 

You do not minimize subjective bias by using this framework, because it is a 
design methodology, and its purpose is to help you exercise your personal judgement
in a systematic way. This is inherently qualitative, because design is inherently
a subjective process. 

## Section 4.9

Also good! 

# Chapter 5 

This is well-done, though you can eliminate the sub-sections!







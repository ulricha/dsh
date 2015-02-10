# Database-Supported Haskell (DSH)

This is a Haskell library for database-supported program
execution. Using DSH, a relational database management system (RDBMS)
can be used as a coprocessor for the Haskell programming language,
especially for those program fragments that carry out data-intensive
and data-parallel computations.

Database executable program fragments can be written using the monad
comprehension notation [2] and list processing combinators from the
Haskell list prelude. Note that rather than embedding a relational
language into Haskell, we turn idiomatic Haskell programs into SQL
queries.

DSH faithfully represents list order and nesting, and compiles the
list processing combinators into relational queries. The
implementation avoids unnecessary data transfer and context switching
between the database coprocessor and the Haskell runtime by ensuring
that the number of generated relational queries is only determined by
the program fragment's type and not by the database size.

DSH can be used to allow existing Haskell programs to operate on large
scale data (e.g., larger than the available heap) or query existing
database resident data with Haskell.

Note that this package is flagged experimental and therefore is not
suited for production use (we mean it!). This is a proof of concept
implementation only. To learn more about DSH, our paper "The Flatter,
the Better — Query Compilation Based on the Flattening
Transformation." [1] is a recommended reading. The package includes a
couple of examples that demonstrate how to use DSH.

The current release does not rely anymore on the loop-lifting
compilation technique and the Pathfinder optimizer. Instead, it brings
a completely rewritten query compiler based on Guy Blelloch's
flattening transformation. This approach leads to a more robust
compilation and produces more efficient query code.

To generate actual code for a relational backend, an additional
backend package needs to be installed. Currently, the package
`dsh-sql` on Hackage provides SQL code generation for PostgreSQL.


1. [http://db.inf.uni-tuebingen.de/publications/TheFlatter-theBetter-QueryCompilationBasedontheFlatteningTransformation.html](Ulrich, Grust. The Flatter, the Better - Query Compilation Based on the Flattening Transformation. Proc. SIGMOD 2015).
2. [http://db.inf.uni-tuebingen.de/staticfiles/publications/haskell2011.pdf](Grust
   et al. Bringing Back Monad Comprehensions. Haskell Symposium 2011).

# Release Notes

* This is an experimental proof-of-concept implementation that most
  likely contains bugs. You have been warned. We are happy to receive
  bug reports.
* For documentation, have a look at the examples included in directory
  'examples' in the source distribution.
* DSH works with a HDBC PostgreSQL connection. Other databases (*e.g.*
  MySQL, Sqlite) are unlikely to work.
* Support for general algebraic data types is currently broken. Flat
  record types do work.
* Comprehension syntax for DSH queries is currently implemented using
  monad comprehensions and the `RebindableSyntax` extension. This
  means that any module that contains DSH queries and makes use of
  comprehension syntax has to enable the extension. Additionally,
  `do`-notation and comprehensions over other monads (*e.g.* lists)
  can not be used in such a module. This limitation is an
  implementation artifact that we hope to get rid of soon.

#lang racket/base
(require scriblib/autobib)
(provide (all-defined-out))

(define-cite ~cite citet generate-bibliography)

(define DVH (author-name "David" "Van Horn"))
(define STH (author-name "Sam" "Tobin-Hochstadt"))
(define PCN "Phúc C. Nguyễn")

(define OOPSLA12
  (proceedings-location "ACM International Conference on
Object-Oriented Programming, Systems, Languages and
Applications (OOPSLA)"))

(define bib:monadic
  (make-bib 
   #:title "Monadic Abstract Interpreters"
   #:author (authors "Ilya Sergey"
		     "Dominique Devriese"
		     "Matthew Might"
		     "Jan Midtgaard"
		     "David Darais"
		     "Dave Clarke"
		     "Frank Piessens")
  #:location (proceedings-location "ACM SIGPLAN Conference on
Programming Language Design and Implementation (PLDI)")
  #:date "2013"))

(define bib:galois-transformers
  (make-bib
   #:title "Galois Transformers and Modular Abstract Interpreters"
   #:author (authors "David Darais"
		     DVH)
   #:location (proceedings-location "ACM International Conference on
Object-Oriented Programming, Systems, Languages and
Applications (OOPSLA)")   
   #:date "2015"))

(define bib:aam-concurrency
  (make-bib
   #:title "A Family of Abstract Interpretations for Static Analysis
of Concurrent Higher-Order Programs"
   #:author (authors "Matthew Might"
		     DVH)
   #:location (proceedings-location "International Static Analysis
Symposium (SAS)")
   #:date "2011"))

(define bib:shivers-phd
  (make-bib
   #:title "Control-Flow Analysis of Higher-Order Languages"
   #:author "Olin Shivers"
   #:location (dissertation-location #:institution "Carnegie Mellon University"
				     #:degree "PhD")
   #:date "1991"))

(define bib:componential
  (make-bib
   #:title "Componential set-based analysis"
   #:author (authors "Cormac Flanagan"
		     "Matthias Felleisen")
   #:location (journal-location "Componential set-based analysis"
				#:volume "21"
				#:number "2")
   #:date "1999"))

(define bib:pdcfa-for-free
  (make-bib
   #:title "Pushdown Control-Flow Analysis for Free"
   #:author (authors "Thomas Gilray"
		     "Steven Lyde"
		     "Michael D. Adams"
		     "Matthew Might"
		     DVH)
   #:location (proceedings-location "ACM SIGPLAN-SIGACT Symposium on
Principles in Programming Languages (POPL)")
   #:date "2016"))

(define bib:pdgc
  (make-bib
   #:title "Introspective Pushdown Analysis of Higher-Order Programs"
   #:author (authors "Christopher Earl"
		     "Ilya Sergey"
		     "Matthew Might"
		     DVH)
   #:location (proceedings-location "ACM SIGPLAN International Conference on Functional Programming (ICFP)")
   #:date "2012"))

(define bib:pdgc-jfp
  (make-bib
   #:title "Pushdown flow analysis with abstract garbage collection"
   #:author (authors "J. Ian Johnson"
		     "Ilya Sergey"
		     "Christopher Earl"
		     "Matthew Might"
		     DVH)
   #:location (journal-location "Journal of Functional Programming"
				#:volume "24"
				#:number "2--3")
   #:date "2014"))

(define bib:aac
  (make-bib
   #:title "Abstracting Abstract Control"
   #:author (authors "J. Ian Johnson"
		     DVH)
   #:location (proceedings-location "ACM Symposium on Dynamic
Languages (DLS)")
   #:date "2014"))

(define bib:cfa2-callcc
  (make-bib
   #:title "Pushdown Flow Analysis of First-Class Control"
   #:author (authors "Dimitris Vardoulakis"
		     "Olin Shivers")
   #:location (proceedings-location "ACM SIGPLAN International
Conference on Functional Programming (ICFP)")
   #:date "2011"))
		     

(define bib:cfa2
  (make-bib
   #:title "CFA2: a Context-Free Approach to Control-Flow Analysis"
   #:author (authors "Dimitris Vardoulakis"
		     "Olin Shivers")
   #:location (journal-location "Logical Methods in Computer Science"
				#:volume "7"
				#:number "2-3")
   #:date "2011"))

(define bib:pdcfa
  (make-bib
   #:title "Pushdown Control-Flow Analysis of Higher-Order Programs"
   #:author (authors "Christopher Earl"
		     "Matthew Might"
		     DVH)

   #:location (proceedings-location "Workshop on Scheme and Functional
Programming (SFP)")
   #:date "2010"))

(define bib:oaam
  (make-bib
   #:title "Optimizing Abstract Abstract Machines"
   #:author (authors "J. Ian Johnson"
		     "Nicholas Labich"
		      "Matthew Might"
		      DVH)

   #:location (proceedings-location "ACM SIGPLAN International
Conference on Functional Programming (ICFP)")
   #:date "2013"))

(define bib:aam-jfp
  (make-bib
   #:title "Systematic Abstraction of Abstract Machines"
   #:author (authors DVH "Matthew Might")
   #:location (journal-location "Journal of Functional Programming"
				#:volume "22"
				#:number "4-5") 
   #:date "2012"))

(define bib:hose
  (make-bib
   #:title "Higher-Order Symbolic Execution with Contracts"
   #:author (authors STH DVH)
   #:location OOPSLA12
   #:date "2012"))
		     

(define bib:anadroid
  (make-bib
   #:title "AnaDroid: Malware Analysis of Android with User-supplied Predicates"
   #:author (authors "Shuying Liang"
		     "Matthew Might"
		     DVH)
   #:location (proceedings-location "Workshop on Tools for Automatic Program Analysis")
   #:date "2013"))

(define bib:js
  (make-bib
   #:title "Pushdown Abstractions of JavaScript"
   #:author (authors DVH
		     "Matthew Might")
   #:location (techrpt-location #:institution "arXiv"
				#:number "109-4467")
   #:date "2011"))

(define bib:jsai
  (make-bib
   #:title "JSAI: A Static Analysis Platform for JavaScript"
   #:author (authors "Vineeth Kashyap"
		     "Kyle Dewey"
		     "Ethan A. Kuefner"
		     "John Wagner"
		     "Kevin Gibbons"
		     "John Sarracino"
		     "Ben Wiedermann"
		     "Ben Hardekopf")
   #:location (proceedings-location "Symposium on Foundations of Software Engineering (FSE)")
   #:date "2014"))

(define bib:entry-point-saturation
  (make-bib 
   #:title "Sound and Precise Malware Analysis for Android via
Pushdown Reachability and Entry-Point Saturation"
   #:author (authors "Shuying Liang"
		     "Andrew W. Keep"
		     "Matthew Might"
		     "Steven Lyde"
		     "Thomas Gilray"
		     "Petey Aldous"
		     DVH)
   
   #:location (proceedings-location "Third ACM workshop on Security
and privacy in smartphones & mobile devices")
   #:date "2013"))


(define bib:gradual-typing-first-class-classes
  (make-bib
   #:title "Gradual Typing for First-Class Classes"
   #:author (authors "Asumu Takikawa"
		     "T. Stephen Strickland"
		     "Christos Dimoulas"
		     "Sam Tobin-Hochstadt"
		     "Matthias Felleisen")
   #:location OOPSLA12
   #:date "2012"))

(define bib:constraining-delim-control
  (make-bib
   #:title "Constraining Delimited Control with Contracts"
   #:author (authors "Asumu Takikawa"
		     "T. Stephen Strickland"
		     "Sam Tobin-Hochstadt")
   #:location (proceedings-location "European Symposium on Programming (ESOP)")
   #:date "2013"))

(define bib:run-your-research
  (make-bib
   #:title "Run Your Research: On the Effectiveness of Lightweight Mechanization"
   #:author (authors "Casey Klein"
		     "John Clements"
		     "Christos Dimoulas"
		     "Carl Eastlund"
		     "Matthias Felleisen"
		     "Matthew Flatt"
		     "Jay A. McCarthy"
		     "Jon Rafkind"
		     "Sam Tobin-Hochstadt"
		     "Robert Bruce Findler")
   #:location (proceedings-location "The 39th Annual ACM SIGPLAN-SIGACT
Symposium on Principles of Programming Languages (POPL)") 
   #:date "2012"))


(define bib:pcf
  (make-bib
   #:title "LCF considered as a programming language"
   #:author "Gordon Plotkin"
   #:date "1977"
   #:location (journal-location "Theoretical Computer Science"
				#:volume "5"
				#:pages (list "223" "255"))
   #:url "http://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf"))

(define bib:redex
  (make-bib
   #:title "Semantics Engineering with PLT Redex"
   #:author (authors "Matthias Felleisen"
		     "Robert Bruce Findler" 
		     "Matthew Flatt")
   #:date "2009" ; July
   #:location (book-location #:publisher "MIT Press")))

(define bib:explicit
  (make-bib
   #:title "Explicit Substitutions"
   #:author (authors "Martín Abadi"
		     "Luca Cardelli"
		     "Pierre-Louis Curien"
		     "Jean-Jacques Lévy")
   #:location (journal-location "Journal of Functional Programming"
				#:volume "1"
				#:number "4"
				#:pages  (list "375" "416"))
   #:date "1991" ; October
   ))

(define bib:muchnick-jones
  (make-bib
   #:title "Program Flow Analysis: Theory and Applications"
   #:author (authors "Steven S. Muchnick"
		     "Neil D. Jones")
   #:location (book-location #:publisher "Prentice Hall")
   #:date "1981"))

(define bib:adi
  (make-bib
    #:title "Abstracting Definitional Interpreters (Functional Pearl)"
    #:author (authors "David Darais"
                      PCN
                      "Nicholas Labich"
                      DVH)
    #:location (proceedings-location "The ACM SIGPLAN International Conference on Functional Programming (ICFP)")
    #:date "2017"))

(define bib:scv-stateful
  (make-bib
    #:title "Soft Contract Verification for Higher-order Stateful Programs"
    #:author (authors PCN "Thomas Gilray" STH DVH)
    #:location (proceedings-location "The 45th ACM SIGPLAN Symposium on Principles of Programming Languages (POPL)")
    #:date "2018"))

(define bib:aam
  (make-bib
   #:title "Abstracting Abstract Machines"
   #:author (authors DVH
		     "Matthew Might")
   #:location (proceedings-location "The 15th ACM SIGPLAN International Conference on Functional Programming (ICFP)")
   #:date "2010" ; September
					;#:url "http://arxiv.org/abs/1007.4446"
   ))

(define bib:counterexamples
  (make-bib
   #:title "Relatively Complete Counterexamples for Higher-Order Programs"
   #:author (authors PCN DVH)
   #:location (proceedings-location "ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI)")
   #:date "2015"))

(define bib:scv
  (make-bib
   #:title "Soft Contract Verification"
   #:author (authors PCN STH DVH)
   #:location (proceedings-location "The ACM SIGPLAN International Conference on Functional Programming (ICFP)")
					;#:url "http://arxiv.org/abs/1307.6239"
   #:date "2014"))

#lang racket
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

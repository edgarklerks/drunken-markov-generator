markov text generator
=====================

A library for creating markov chains from text and generate new string from the markov model. Good for creating spam messages and general amusement. It is easy to extend the markov model analyzer for non text related tasks.

It can generate markov models from an url. It can be extended by providing an new instance to the Order  class.

I supplied a composable variant MarkovArrow, which probably isn't an arrow, but I am not sure, I have to check the laws for that. 

I am quite sure it is a category, a functor and a applicative (of the cross product variant). This would the user give the possibility to compose the markov model. Every markov model can be lifted as an markov arrow.  

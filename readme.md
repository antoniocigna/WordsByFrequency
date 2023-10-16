Words by Frequency
------------------

Antonio Cigna 2023

**WARNING work in progress, there is no documentation and most of the messages are in Italian**

This application (which works only on Windows desktop) has been created as a tool to improve the understanding of a foreign language.

It reads text file which can be very large (tested with 100,000 rows) and extracts all sentences and words in it.

You need a "word-lemma" file (lemma is the term you can look for in a dictionary) which for each word associate its lemmas.

It is possible to request:

* the list of the most used words: all words are sorted in decreasing order of use (first the number the most used)
* the list of words with the same prefix
* the list of words with the same lemma

For each word it is possible to read its translation (by moving the mouse) or to list the sentences containing it

It is also possible to list

* all sentences which contain a specified word
* all sentences in the same order as appear in the text

It is possible to require the reading by a synthetic voice of words and sentences.
  
**Software**
*   Start.bat               - a file to call the exe file   
*   wordsByFrequency.exe    - reads/writes files and does he heavy work ( the program is written in **go** language)    
*   wordByFrequency.html,   wordByFrequency.js and other html/javascript files ( to manage user requests )   
  
     
  
  
**Antonio Cigna**  
October 16, 2023
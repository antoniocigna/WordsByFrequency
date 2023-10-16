"use strict";
/*  
LineByLine: A tool to practice language comprehension
Antonio Cigna 2023
license MIT: you can share and modify the software, but you must include the license file 
*/
/* jshint strict: true */
/* jshint esversion: 6 */
/* jshint undef: true, unused: true */
//----------------------------------------------
var currScript = document.currentScript.src; var bar1 = currScript.lastIndexOf("\\");var bar2 = currScript.lastIndexOf("/"); 
//console.log("LOADED file SCRIPT " + currScript.substring( 1+Math.max(bar1,bar2) )) ;	
//----------------------------------------------------------------------------------------
/***
	may be the case that a synthetic voice for a language does not exist ( eg. in case of a dead language as latin )
    this function try to solve this problem 
			by changing the text so that it read by an other language voice can sounds like the original one
			
	for instance: latin word 'coeli' modified in 'celi' to be read by an Italian voice sounds as ecclesiastical Latin.   
	
**/
//----------------------------------------------------------------------------------------
function tts_8_REPLACE( txt1 ) {  
	// this function is called for each original language line text
   	// if tts text is equal to the original then this function should return "" 
	//
	// this function should be driven by the array 'language_parameters'; 
	//                         language_parameters[0] language id of the voice
	//                         language_parameters[1] number of voices 
	//						   language_parameters[2,...] routine to use and other parameters if needed
	//
	//-----------------------------------------	
	// eg. var  tts_txt = txt1.replaceAll("oe","e");  return tts_txt;  
	
	return ""; 
	
} // end of add_text_to_be_spoken_line()
//----------------------------------------------------------

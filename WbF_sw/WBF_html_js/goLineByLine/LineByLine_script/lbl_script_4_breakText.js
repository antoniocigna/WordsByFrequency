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

function tts_4_split_into_rows(inpTxt, maxRowLen) {

    var newText = inpTxt.trim().replaceAll("  ", " ").replaceAll("  ", " ").replaceAll("  ", " ").replaceAll("  ", " ").replaceAll("  ", " ").
	replaceAll("?","?\n").replaceAll("!","!\n").
    replaceAll(". ", ". \n").replaceAll(" \n", "\n").replaceAll("\n\n", "\n");
    var rows = newText.split("\n");

	var txt2 = "";	
	var txtOut=""
    for (var z1 = 0; z1 < rows.length; z1++) {
	
		txt2 = tts_4_words_from_one_line(rows[z1], "1 "+ z1).trim();
		
		if ((txt2 == "") || (txt2 == "\n"))  continue;
		txtOut += "\n" + txt2;
    }	
	
	return txtOut.substring(1); 
	
	//----------------------------
	
    function tts_4_words_from_one_line(rowOne, wh) {
		
		var textOut = "";       
		var woFS = rowOne.split(". ");
		var wo, wo00, wo1, wo1X, zx, z2, j1;
		
		wo00 = rowOne.trim();
		
		for (zx = 0; zx < woFS.length; zx++) {		
			wo00 = woFS[zx].trim();
			if (wo00 == "") break; 
						
			for(var b=0; b < wo00.length; b++) { 
				//if (b > 50) break;
				wo1 = wo00.trim(); 
				
				if (wo1 == "") break; 
				if (wo1.length <= maxRowLen) {
					textOut+="\n" + wo1;					
					break;					
				} 
				wo1X = wo1.substring(0,maxRowLen); 

				j1 = wo1X.lastIndexOf(";");
				if (j1 < 0) {j1 = wo1X.lastIndexOf(","); }
				if (j1 >=0) j1++;  				
				if (j1 < 0) {j1 = wo1X.lastIndexOf(" "); }
				if (j1 < 0) { // no comma, neither space backward, try forward 
					j1 = (wo1+" ").indexOf(" "); 
				}
				
				wo00 = wo1.substring(j1);
				textOut+="\n" + wo1.substring(0,j1); 	
			}
		}		
		return textOut;
    } // end of  words_from_one_line()   

} // end of  split_into_rows()

//==================================================
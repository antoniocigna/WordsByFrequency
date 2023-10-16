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

function NOT_USED_tts_9_get_wantedVoices_from_URL_parameters() { 

	// eg. file:///D:/ANTONIO/ClipByClip_V2/cbc_base/cbc_player/cbc_PLAYER.html?p_title=OneLesson
	
	// this function is called in script_9... file 
	
	
	//console.log("\nXXXXXXXXXXXXXXXXXXXXXXXXXX\nX get_html_URL_parameters() \nXXXXXXXXXXXXXXXXXXXXXXXXXX\n"); 
	
	html_parms_queryString = window.location.search;
	console.log("window.location.search = html_parms_queryString="  +  html_parms_queryString);
	
	if ((html_parms_queryString == undefined ) || (html_parms_queryString.trim() == "") ) {	
		return; 	
	} 	
	const urlParams = new URLSearchParams(html_parms_queryString);		
	var selected_language_fromBuilder = decodeURI( urlParams.get("p_sel_voicelang" ) );    // eg.  en,6
	console.log("selected_language_fromBuilder = " + selected_language_fromBuilder);  
	if (selected_language_fromBuilder == "null") {
		language_parameters = ["xx","0"];  
		selected_lang_id = "xx"; 
		selected_numVoices=0;  	
	} else { 	
		language_parameters = (selected_language_fromBuilder+",,,").split(","); 
		selected_lang_id    = (language_parameters[0]+"   ").trim(); // .substr(0,2); 
		selected_numVoices  = parseInt("0" + language_parameters[1].trim() )  ; 		 
	}
	if (selected_numVoices > maxNumVoices)  selected_numVoices = maxNumVoices;
	
	console.log("parameters from Builder: language '" + selected_lang_id  + "' num.Voices=" + selected_numVoices); 
	
} // end of  get_wantedVoices_from_URL_parameters()

//------------------------------------
function tts_9_toBeRunAfterGotVoicesPLAYER() { 
	console.log(" tts_9_toBeRunAfterGotVoicesPLAYER()")
	//
	// called by asynchronous code in fcommon_load_all_voices()  (if numVoices > 0) 
	//
	//-------------------------------------
	//console.log("script_9 toBeRunAfterGotVoices()"); 	
	//console.log("script_9 voices.length=" + voices.length);
	
	tts_2_fill_the_voices();  //  in script_2... file  
	
	string_tr_xx = "\n" + prototype_tr_m2_tts + "\n" + prototype_tr_m1_tts + "\n" + prototype_tr_tts; 
	word_tr_allclip =  "\n" + prototype_word_tr_m2_tts + "\n" + prototype_word_tr_m1_tts + "\n" + prototype_word_tr_tts; 
		
	tts_3_getUrlData3(); 	
	
	//--------------------
} // end of toBeRunAfterGotVoices() 	

//=============================================

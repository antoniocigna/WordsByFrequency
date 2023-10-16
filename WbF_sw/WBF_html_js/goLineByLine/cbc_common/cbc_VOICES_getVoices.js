"use strict";
/*  
ClipByClip: A tool to practice language comprehension
Antonio Cigna 2021/2022
license MIT: you can share and modify the software, but you must include the license file 
*/
/* jshint strict: true */
/* jshint esversion: 6 */
/* jshint undef: true, unused: true */
//----------------------------------------------
var currScript = document.currentScript.src; var bar1 = currScript.lastIndexOf("\\");var bar2 = currScript.lastIndexOf("/"); 
//console.log("LOADED file SCRIPT " + currScript.substring( 1+Math.max(bar1,bar2) )) ;	
//----------------------------------------------------------------------------------------

//-----------------------------------------------

let numLoadVoiceIteration=0 ;
//-----------------------------------

function fcommon_load_all_voices() {

	console_log_1("xxxxxxxxxxxxxxxxxxxx  load_all_voices:  interation "  + (1+numLoadVoiceIteration) );  
	//---------------------------------
	function voices_load_ok(voices) {		
		var numLocal =0;
		var numRemote =0;
		for(var g=0; g < voices.length; g++) {
			//console.log(voices[g].name); 
			if (voices[g].localService) {
				numLocal ++;
			} else {
				numRemote++;
			}
		}
		//----------
		//console_log_1( voices.length + " voices loaded: " + numLocal + " local, " + numRemote + " remote" );
		
		if ((numLocal < 1) || (numRemote < 1)) {
			if (numLoadVoiceIteration < 2) {
				numLoadVoiceIteration++ ;
				setTimeout(fcommon_load_all_voices, 500);
			} else {
				// too many unsuccessful attempts, get what there is; 
				use_the_voices();
			}
		} else {   
			//console.log("== ok == " + numLoadVoiceIteration); 
			use_the_voices();
		}
	} // end of load_ok
	//---------------------------------
	function voices_load_error(error) {
		console.log("error in loading voices"); 
	}
	//---------------------------------
	const allVoicesObtained = new Promise(
					function(resolve, reject) {
						  //	console.log("cbc_VOICES_getVoices.js fcommon_load_all_voices()  allVoicesObtained"); 
						  voices = window.speechSynthesis.getVoices();
						  if (voices.length !== 0) {
							resolve(voices);
						  } else {
							window.speechSynthesis.addEventListener("voiceschanged", function() {
							  voices = window.speechSynthesis.getVoices();
							  resolve(voices);
							});
						  }
					}
			);
	allVoicesObtained.then(
		function(voices) { voices_load_ok(voices);   },
		function(error)  { voices_load_error(error);}
	);
	//----------------------------------
	function use_the_voices() {
		/**
		for(var g=0; g < voices.length; g++) {
			console.log("\t" + voices[g].lang + " " + voices[g].name + " \t localService=" + voices[g].localService); 
		}
		**/
		//console.log("cbc_VOICES_getVoices.js fcommon_load_all_voices()  use the voices() "); 
		
		tts_1_toBeRunAfterGotVoices(); 
		tts_2_fill_the_voices() 
	}	
	//-----------------------------
} // end of load_all_voices()
//==============================================================

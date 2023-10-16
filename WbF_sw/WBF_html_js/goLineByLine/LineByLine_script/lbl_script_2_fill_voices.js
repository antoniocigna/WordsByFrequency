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
/*
let selected_voice_ix                    = 0 ;     // eg. 65 	 
let selected_voiceName                   = "";     // eg. Microsoft David - English (United States)"; 	
let	selected_voiceLangRegion             = "";     // eg. en-us	
let	selected_voiceLang2                  = "";     // eg. en
*/
//======================================	
function tts_2_fill_the_voices() { 
	
	//console.log("\nxxxxxxxx\nxx tts_2_fill_the_voices()\nxxxxxxx");
	
	var numTotVoices = voices.length
	/**
	console.log("voices.length=" + numTotVoices); 
	console.log("voices[0]=" + voices[0].name); 
	console.log("voices["+(numTotVoices-1)+"]=" + voices[(numTotVoices-1)].name); 
	**/
	for(var ix=0; ix < numTotVoices; ix++) {
		if (selected_voiceName == voices[ix].name) {
			selected_voice_ix        = ix; 	
			selected_voiceLangRegion = voices[ix].lang	
			selected_voiceLang2      = selected_voiceLangRegion.substr(0,2);
			//selected_voiceName     = voices[ix].name
			break;
		}
		
	}
	var vox;
	listVox = [];
	
	if (selected_voice_ix == 0) { return; }
	
	//firstly the chosen language-voice
	vox = voices[selected_voice_ix];
	 
	listVox.push( [vox.lang , vox] );  
	if (selected_voiceLangRegion != vox.lang) {
		console.log("tts_2_fill_the_voices() " + "\n\tselected_voice_ix=" + selected_voice_ix + 
			"\n\tselected_voiceName = " + selected_voiceName +
			"\n\tselected_voiceLangRegion = " + selected_voiceLangRegion +
			"\n\tselected_voiceLang2 = " + selected_voiceLang2); 
		console.log("ERROR vox.lang (from voices[selected_voice_ix]) = " + vox.lang  + 
				" vs " + "selected_voiceLangRegion=" +selected_voiceLangRegion);  
		console.log(signalError)		
	}
	
	//------------------------------------------
	// secondly the same language-region 
	for(var v2=0; v2 < voices.length; v2++) {
		vox = voices[v2];
		if (v2 == selected_voice_ix) continue; 
		
		if (selected_voiceLangRegion != vox.lang ) continue;	
		
		listVox.push( [vox.lang , vox] );  		
	}
	//---------------------------------	
	// thirdly the same language
	for(var v2=0; v2 < voices.length; v2++) {
		vox = voices[v2];
		if (selected_voiceLangRegion == vox.lang ) continue;	
		if (selected_voiceLang2 != vox.lang.substr(0,2) ) continue;				
		listVox.push( [vox.lang , vox] );  
	}
	//---------------------------------	
	//
	for(v3=0; v3 < listVox.length; v3++) {		
		var vv1, vv2; 
		[vv1,vv2] = listVox[v3]
		//console.log("listVox[" +v3 + "] = " + vv1 + " " + vv2.name);
	}
	//----------------	
	var chosenIxVox=0;
	//-----------
	if (listVox.length == 0) {
		return; 
	}
	//console.log("listVox length=" + listVox.length); 
	voice_toUpdate_speech = listVox[0][1] ;	

	
	var voxLang;
	var pVox = ""; var xbr; 
	var vv3=0; var v3;
	var idhvox, idh2, eleH; 
	totNumMyLangVoices = listVox.length;
	
 	
} // end of fill_the_voices()



//======================================	
function TOGLItts_2_fill_the_voices() { 
	
	console.log("voices.length=" + voices.length); 
	
	var vox;
	listVox = [];
	
	//firstly the chosen language-voice
	vox = voices[selected_voice_ix];
	 
	listVox.push( [vox.lang , vox] );  
	if (selected_voiceLangRegion != vox.lang) {
		console.log("tts_2_fill_the_voices() " + "\n\tselected_voice_ix=" + selected_voice_ix + 
			"\n\tselected_voiceName = " + selected_voiceName +
			"\n\tselected_voiceLangRegion = " + selected_voiceLangRegion +
			"\n\tselected_voiceLang2 = " + selected_voiceLang2); 
		console.log("ERROR vox.lang (from voices[selected_voice_ix]) = " + vox.lang  + 
				" vs " + "selected_voiceLangRegion=" +selected_voiceLangRegion);  
		console.log(signalError)		
	}
	
	//------------------------------------------
	// secondly the same language-region 
	for(var v2=0; v2 < voices.length; v2++) {
		vox = voices[v2];
		if (v2 == selected_voice_ix) continue; 
		
		if (selected_voiceLangRegion != vox.lang ) continue;	
		
		listVox.push( [vox.lang , vox] );  		
	}
	//---------------------------------	
	// thirdly the same language
	for(var v2=0; v2 < voices.length; v2++) {
		vox = voices[v2];
		if (selected_voiceLangRegion == vox.lang ) continue;	
		if (selected_voiceLang2 != vox.lang.substr(0,2) ) continue;				
		listVox.push( [vox.lang , vox] );  
	}
	//---------------------------------	
	//
	for(v3=0; v3 < listVox.length; v3++) {		
		var vv1, vv2; 
		[vv1,vv2] = listVox[v3]
		console.log("listVox[" +v3 + "] = " + vv1 + " " + vv2.name);
	}
	//----------------	
	var chosenIxVox=0;
	//-----------
	if (listVox.length == 0) {
		return; 
	}
	console.log("listVox length=" + listVox.length); 
	voice_toUpdate_speech = listVox[0][1] ;	

	
	var voxLang;
	var pVox = ""; var xbr; 
	var vv3=0; var v3;
	var idhvox, idh2, eleH; 
	totNumMyLangVoices = listVox.length;
	
 	
} // end of fill_the_voices()

//--------------------------
function test_theVoice(lang2, myVoice) {
	if (lang2 == myVoice.lang.substr(0,2) ) return true;  
	
} // end of test_theVoice()

//====================================== 
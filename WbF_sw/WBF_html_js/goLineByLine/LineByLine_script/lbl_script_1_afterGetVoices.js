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

  var page1 = document.getElementById("page1");
  var page2 = document.getElementById("page2");

 
//---------------------------------	
  var builder_orig_subtitles_string = "";
  var builder_tran_subtitles_string = "";

  var sw_inp_sub_orig_builder = false;
  var sw_inp_sub_tran_builder = false;

  const TRANSLATION_NOT_WANTED = "...";
 
  var sw_translation_not_wanted = false;
  var selected_voice_language = "XX,0,0"; //  language id, number of voices eg. en-GB Microsoft ...  , index of chosen voice 
  
  //===============================
  var myVoice;
  let voices;
  //----------------------


  //fcommon_load_all_voices();  // at end calls tts_1_toBeRunAfterGotVoices()

  // WARNING: the above function contains asynchronous code.  
  // 			Any statement after this line is executed immediately without waiting its end


 // test voice with previous run
 function testPrevVoice() {

	if (prev_voiceName == "") { return -1; }
	
	for (var z1 = 0; z1 < voices.length; z1++) {
		if (voices[z1].name == prev_voiceName) return z1;	
	}	
	for (var z1 = 0; z1 < voices.length; z1++) {
		if ( voices[z1].lang == prev_voiceLangRegion) return z1	;
	}		
	for (var z1 = 0; z1 < voices.length; z1++) {
		if ( voices[z1].lang.substring(0,2) == prev_voiceLang2) return z1;	
	}	
	return -1;
 }
 
 //-------------------------------------------------
  function tts_1_toBeRunAfterGotVoices() {
	  //	console.log("tts_1_toBeRunAfterGotVoices() ")
      if (voices.length < 1) return;

      voices.sort(
          function(a, b) {
              return ((a.lang + a.name) > (b.lang + b.name)) ? 1 : -1;
          }
      );
	  
	  //------------------	   
      var pLang2 = "??";
      var pLang4;
      var numL2 = 0;
      var numL4 = 0;
	  var langName;
      var ixSele = -1;
	  var sele_str = "";
	  var selected_yes="selected"; 
	  var swSele=false; 
	  var voice_name =""; 

	  var ixPrevFound = -1 
	  
	  
	  if (prev_voiceName != "") {  
			ixPrevFound = testPrevVoice() 
	  }
	  
	  /**
	  if (ixPrevFound < 0) {
			console.log("tts_1_toBeRunAfterGotVoices()  ixPrevFound not found"); 
	  } else {  
			console.log("tts_1_toBeRunAfterGotVoices()  ixPrevFound=" + ixPrevFound, "\nlastRunLanguage=" +  lastRunLanguage);
	  }
	  **/
	  
	  sele_str += '      <option value="' + 9999+ '" selected>' + '--' + " " + "----------"  +  '</option> \n';
	  
      for (var z1 = 0; z1 < voices.length; z1++) {
		  swSele = false; 
          var lang = voices[z1].lang;
          var lang2 = lang.substr(0, 2);
          if (lang != pLang4) {
              //console.log(lang);
              numL4++;
              if (lang2 != pLang2) {
				  langName = get_languageName(lang).split("-")[0].trim(); 
                  numL2++;
                  sele_str += '   </optgroup> \n';
                  sele_str += '   <optgroup label="' + lang2 + ' ' + langName + '"> \n';
              }
          }
		  /**
		  if (lang == "NONEen-GB") {
				if (ixPrevFound < 0) {
					if (ixSele < 0) {
						ixSele=z1;
					}	
				}
		  }
		  **/
		  
		  voice_name = voices[z1].name;
	  	 
		  if ((ixSele == z1 ) || (ixPrevFound == z1)) {
				sele_str += '      <option value="' + z1 + '" selected>' + lang + " " + voice_name +  '</option> \n';
		  } else {
			  sele_str += '      <option value="' + z1 + '">' + lang + " " + voice_name +  '</option> \n';
		  }	
		 
          pLang4 = lang;
          pLang2 = lang2;
      }	  
	  
	  pLang4 = lang;
      sele_str += '   </optgroup> \n';
	  
      let voiceSelect = document.getElementById("id_voices");
      voiceSelect.innerHTML = sele_str;
	  /**	
	  for(var g1=0; g1 < voiceSelect.children.length; g1++) {
		  var gr1 = voiceSelect.children[g1]; 
		  console.log("voiceSelect " + g1 + " gr1= " + gr1.outerHTML);    
	  } 
	  **/	  
   	  if (ixPrevFound < 0) {
		  onclick_tts_get_oneLangVoice(  voiceSelect );	  
	  } else {
		  document.getElementById("id_divVoice").style.display = "none"; 
		  onclick_tts_get_oneLangVoice(  ixPrevFound );	  
	  }	  
	
	  
  } // end of toBeRunAfterGotVoices()

  //===============
  //--------------------------------------------------
 function tts_1_get_orig_subtitle2() {
      /**
	
         console.log("get_orig" + "\n\t value=" +  document.getElementById("txt_pagOrig").value +
         						"\n\t fromText_to_srt=" +  fromText_to_srt(   document.getElementById("txt_pagOrig").value.trim() )  ); 
         **/
      var msgerr1 = "";
    
      builder_orig_subtitles_string = document.getElementById("txt_pagOrig").value.trim();
      if (builder_orig_subtitles_string != "") {
          sw_inp_sub_orig_builder = true;
      } else {
          sw_inp_sub_orig_builder = false;
          msgerr1 += "<br>" + tts_1_getMsgId("m132"); //  ma22 the source language subtitle file  has not been read or is empty" ;         
      }
	  inp_row_orig = builder_orig_subtitles_string.split("\n") ;
	  inp_row_orig.push("");    
	  numOrig = inp_row_orig.length;
	
      return msgerr1;

  } // end of get_orig_subtitle2()
  //--------------------------------------------------

  function tts_1_get_tran_subtitle2(msgerrOrig) {
      /**
      	console.log("get_tran" + "\n\t value=" +  document.getElementById("txt_pagTrad").value +
      						"\n\t fromText_to_srt=" +  fromText_to_srt(    document.getElementById("txt_pagTrad").value.trim() )  ); 
      **/
      var msgerr1 = "";

      //builder_tran_subtitles_string = fromText_to_srt(  document.getElementById("txt_pagTrad").value.trim() );
      builder_tran_subtitles_string = document.getElementById("txt_pagTrad").value.trim();
      sw_inp_sub_tran_builder = false;
      if (builder_tran_subtitles_string != "") {
          sw_inp_sub_tran_builder = true;
      } else {
          sw_inp_sub_tran_builder = false;
          if (sw_translation_not_wanted == false) {
			  //console.log("anto1   msgerrOrig=" + msgerrOrig)
              msgerr1 += "<br>" + tts_1_getMsgId("m133"); //    translated subfile missing     					
              if (msgerrOrig == "") { // only if original srt is Ok  
                  msgerr1 += "<br>" + tts_1_getMsgId("m134").replace("§...§", TRANSLATION_NOT_WANTED); // if there is no translation
			  }
          }
      }
	  inp_row_tran = builder_tran_subtitles_string.split("\n");
	  inp_row_tran.push(""); 
	  numTran = inp_row_tran.length;  
	  
      return msgerr1;

  } // end of tts_1_get_tran_subtitle2()

  //--------------------------
  function tts_1_join_orig_trad() {
	  
	  console.log("tts_1_join_orig_trad()") 
	  
      document.getElementById("id_msg16").innerHTML = "";

      sw_translation_not_wanted = false;

      var msgerr0 = "";
      var msgerr1 = tts_1_get_orig_subtitle2(); // get orig. text /srt
      var msgerr2 = tts_1_get_tran_subtitle2(msgerr1); // get tran. text/srt	

      msgerr0 += msgerr1 + msgerr2;
      var msgerr3 = "";

      msgerr0 += msgerr3;

      if (msgerr0 != "") {
          tts_1_putMsgerr(msgerr0);
          document.getElementById("id_msg16").style.color = "red";
          return -1;
      }
      document.getElementById("id_msg16").style.color = null;

      //console.log("ORIG =" + builder_orig_subtitles_string);
      //console.log("TRAN =" + builder_tran_subtitles_string);
	  
	  //tts_1_get_wantedVoices_X();  	
	  
	  tts_9_toBeRunAfterGotVoicesPLAYER(); 

      return 0;

  } // end of tts_1_join_orig_trad()

  //----------------------

  function tts_1_putMsgerr(msgerr1) {
      if (msgerr1 == "") {
          document.getElementById("id_msg16").style.display = "none";
      } else {
          if (msgerr1.substring(0, 4) == "<br>") {
              msgerr1 = msgerr1.substring(4);
          }
          document.getElementById("id_msg16").innerHTML = msgerr1;
          document.getElementById("id_msg16").style.backgroundColor = "white";
          document.getElementById("id_msg16").style.display = "block";
      }

  } // end of putMsgerr()

  //--------------------------------

  function tts_1_getMsgId(id1) {  
	var ele1 = document.getElementById(id1);  
	if (ele1 == null) {		
		console.log("msg " + id1 + "  tts_1_getMsgId() non trovato"  );
		return "";
	}	
    return ele1.innerHTML;
  }
//-------------------------------------
/*
	let selected_voice_ix                    = 0 ;     // eg. 65 	 
	let selected_voiceName                   = "";     // eg. Microsoft David - English (United States)"; 	
	let	selected_voiceLangRegion             = "";     // eg. en-us	
	let	selected_voiceLang2      
*/  
//-------------------------

function tts_1_get_wantedVoices_X() { 
 
	if (selected_voice_language == "null") {
		language_parameters = ["xx","0","0"];  
		selected_lang_id = "xx"; 
		selected_numVoices=0;  	
	} else { 	
		language_parameters = (selected_voce_language+",,,").split(","); 
		selected_lang_id    = (language_parameters[0]+"   ").trim(); // .substr(0,2); 
		selected_numVoices  = parseInt("0" + language_parameters[1].trim() )  ; 		
			
	}
	if (selected_numVoices > maxNumVoices)  selected_numVoices = maxNumVoices;
	
	console.log("parameters from Builder: language '" + selected_lang_id  + "' num.Voices=" + selected_numVoices); 
	
} // end of  get_wantedVoices_X()

//-------------------------------------
function tts_1_get_languagePlayer(ix) {

	var aVoice = document.getElementById("id_myLang").innerHTML;
	var voi = aVoice.split(" ");
	var voice2 = voi[0]; 	
	var voiceL = voice2.length;
	var nn=0;
	for(var g=0; g < voices.length; g++) {
		var myVoice = voices[g].lang;
		if (myVoice.substr(0,2) == voice2.substr(0,2) ) {			
			nn++; 
		}  
	}
	selected_voice_language = voice2 + "," + nn + "," + ix; 
	var lan1 = document.getElementById("m002").innerHTML ;
	var lan2 = document.getElementById("m003").innerHTML
	document.getElementById("id_lang2").innerHTML = "  (" + lan1 + " " + voice2 + ", " + nn + " " + lan2 + ")" ;
	
	//console.log("tts_1_get_languagePlayer(ix) " + " voices.length=" + voices.length + 
	//	"\n\t  selected_voice_language=" + selected_voice_language + "\n\t id_lang2 = " +document.getElementById("id_lang2").innerHTML ); 
	
	writeLanguageChoise(); // in file "wordsByFrequence.js"  	
		
		
} // end of get_language()

//--------------

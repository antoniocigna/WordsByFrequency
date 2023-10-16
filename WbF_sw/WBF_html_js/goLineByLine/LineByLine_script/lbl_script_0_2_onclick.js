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

function onclick_tts_getOrigTxt() {
	
	var ele_inp = document.getElementById("inp_txtOrig00");	
	var input_text = ele_inp.value;
	
	if (is_srt(input_text) ) {
		var rigaFrom, rigaTo, rigaTxt, idsrt;
		[rigaFrom, rigaTo, rigaTxt, idsrt] = get_subtitle_strdata( input_text );
	    input_text = rigaTxt.join("\n").trim(); 
	} 
	
	var output_text;
	var maxRowLen = document.getElementById("id_maxLeng").value; 
	if (maxRowLen < 999) { 			
		output_text = tts_4_split_into_rows(input_text, maxRowLen);
	} else {
		output_text = input_text; 
	}
	
	//document.getElementById("inp_txtOrig00").value = output_text;
	document.getElementById("txt_pagOrig").value = output_text.trim();
	document.getElementById("page0").style.display = "none"; 
	document.getElementById("page1").style.display = "block"; 
	
	function is_srt(input_text1) {
		var numsrt = ( input_text1.replace("- ->", "-->").replace(" -> ", " --> ").replace("-- >", "-->") ).indexOf(" --> "); 
		return ( numsrt > 0); 
	}	
	
} // end of onclick_tts_getOrigTxt()

//-------------

function onclick_tts_get_oneLangVoice(this1) {
	
	//console.log("\nx\nx\nxxxxxxxxxxxxxxx " + " onclick_tts_get_oneLangVoice() \nxxxxxxxxxxxxxxx")
	
	var ix=-1;
	if ( typeof this1 == "object" ) { 
		ix = this1.value; 
	} else {
		ix = this1 
	}	

	if (listVox.length > 0) {  // if this is not the first language setting    
		//console.log("\nx\nx\nxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\nfill the voices again \nxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n") 
		tts_2_fill_the_voices();  //  tts_9_toBeRunAfterGotVoicesPLAYER();
	}
	var langRegion ="";
	try{
		langRegion = get_languageName( voices[ix].lang ) ;
	} catch(e1) {
		return		
	}	
	 
	var langname = langRegion.split("-")[0]; 
	document.getElementById("id_ext_language").innerHTML = voices[ix].lang + " " + langRegion; // in common/cbc_MESSAGE_manager.js 
	
	//document.getElementById("id_laName").innerHTML  =  langname ;
	document.getElementById("id_laName2").innerHTML =  langname ;
	//document.getElementById("m016-1").innerHTML  =  document.getElementById("m016").innerHTML.replace("§1§", langname);
	document.getElementById("m138-1").innerHTML  =  document.getElementById("m138").innerHTML.replace("§1§", langname);
	
	myVoice = voices[ix].lang + " " + voices[ix].name;  
	document.getElementById("id_myLang").innerHTML = myVoice;  
	selected_voice_ix        = ix; 	
	selected_voiceLangRegion =  voices[ix].lang	
	selected_voiceLang2      =  selected_voiceLangRegion.substr(0,2);
	selected_voiceName       =  voices[ix].name
	writeLanguageChoise()   // in wordsByFrequence.js 
	tts_3_show_speakingVoiceFromVoiceLangName(selected_voiceLangRegion, selected_voiceName);
		
	//console.log("onclick_tts_get_oneLangVoice() " + " selected_voice_ix=" + selected_voice_ix + "  id_my_lang = myVoice =" + myVoice);  
	
	isVoiceSelected = true; 
	tts_1_get_languagePlayer(ix); 
	   
} // 

//------------------------------------------------------------------------

function onclick_tts_getInput(elepage) {

  if (tts_1_join_orig_trad() < 0) {
	  return;
  }

  var elepage1 = document.getElementById("page1");
  var elepage2 = document.getElementById("page2");
  if (elepage == elepage1) {
	  elepage2.style.display = "block";
  } else {
	  elepage1.style.display = "block";
  }
  elepage.style.display = "none";
}
    
//-------------------------------------------------

function onclick_tts_arrowFromIx( this1, z3, wh) {
	//------------------------------------------
	// button from ( --> ) has been clicked 
	//------------------------------------------

	//console.log(" onclick_tts_arrowFromIx( this1, z3=" +z3 + ", wh=" + wh); 
	
	tts_5_removeLastBold(); 
	tts_5_fun_invisible_prev_fromto(-1);
	
	fromIxToIxLimit = [z3 ,-1]; 
	[begix, endix] =  fromIxToIxLimit;
	
	tts_5_fun_copy_openClose_to_tr_m1(z3) ;  //  copy open/Close book style from this line idtr_xx to the upper idtr_xx_m1
	
	fromIxToIxButtonElement=[this1, null];
	this1.style.backgroundColor = "green";	

} // end of  onclick_tts_arrowFromIx()  

//---------------------------------------

function onclick_tts_arrowToIx( this1, z3 ) {
	//------------------------------------------
	// button to( <-- ) has been clicked 
	//------------------------------------------
	
	
	//reset previous ..._ToIx  button     
		
	if (fromIxToIxButtonElement[1]) {
		fromIxToIxButtonElement[1].style.backgroundColor = null;
		var endix2 = fromIxToIxLimit[1]; 
		if (endix2 > 0)  {
			var id_post_tr_end_space2 = "idtr_" + (endix2+1) + "_m2" ; 
			if (document.getElementById(id_post_tr_end_space2  ) ) { document.getElementById(id_post_tr_end_space2 ).style.display = "none"; }
		}
	}
	//-------------------------------------------
	// new ... _ToIx
	
	fromIxToIxLimit[1]   = z3;  
	fromIxToIxButtonElement[1] = this1;
	
	[begix, endix] = fromIxToIxLimit;	
	
	/*
	this:  from id="b1_§1§" fromIx(§1§,this) -  to id="b2_§1§" 
		<tr id="idtr_§1§_m2"  ...>
		<tr id="idtr_§1§_m1"  ...>
	**/
	
	var id_pre_tr_beg_space  = "idtr_" + begix + "_m2" ; 
	var id_pre_tr_head       = "idtr_" + begix + "_m1" ; 
	var id_post_tr_end_space = "idtr_" + (endix+1) + "_m2" ; 
	
	tts_5_fun_copyHeaderSelected() ; 
	
	
	if (document.getElementById(id_pre_tr_beg_space ) ) {  
		document.getElementById(id_pre_tr_beg_space).style.display = "table-row";  
		if (begix < 2) 
			document.getElementById(id_pre_tr_beg_space).style.display = "none";  
	}
	//else {console.log(" manca "+id_pre_tr_beg_space ) }	
	if (document.getElementById(id_pre_tr_head      ) ) {  document.getElementById(id_pre_tr_head     ).style.display = "table-row"; }	
	//else {console.log(" manca "+id_pre_tr_head      ) }	
	if (document.getElementById(id_post_tr_end_space) ) { document.getElementById(id_post_tr_end_space).style.display = "table-row";}
	//else {console.log(" manca "+id_post_tr_end_space ) }	

	this1.style.backgroundColor="red";
	
	//c_onsole.log("onclick_tts_arrowToIx() calls 'fun_reset_clip_all_sel()'" )  ; 
	
	//21 novembre // fun_reset_clip_all_sel();
	
	
	
} // end of onclick_tts_arrowToIx()

//------------------------------------------


function onclick_tts_playSynthVoice_row2(this1, ixTD123, swPause,swNewVoice) {
		//console.log("1 onclick_tts_playSynthVoice_row2()  "  , " totNumMyLangVoices=", totNumMyLangVoices  ); 
		if (tts_3_play_or_cancel(this1) < 0) {
				return;
			}	
	
		if (swNewVoice) {
			lastNumVoice++; 
			if (lastNumVoice >= totNumMyLangVoices) lastNumVoice = 0; // to change voice on each cycle
		} else {
			lastNumVoice = 0; 
		}		
	    //console.log("2 onclick_tts_playSynthVoice_row2() lastNumVoice=" + lastNumVoice);  
	    voice_toUpdate_speech = listVox[lastNumVoice][1]  ;  
		 
		 var td1 = this1.parentElement;
	     var tr1 = td1.parentElement;
		 
	     var txt1 = "",
	         txt2 = "";

		//console.log("3 onclick_tts_playSynthVoice_row2()"); 	
		
		 if (tr1.id.substr(0,5) == "idtr_") {
				var numId= tr1.id.substring(5);
				var ele_txt = document.getElementById("idc_"+ numId); 
				
				//console.log("??anto numId=", numId,  " ele_txt=" , ele_txt, " \n\tele_txtx.innerHTML=" , ele_txt.innerHTML );  
				if (ele_txt == null) return;
				var ele_tts = document.getElementById("idtts" + numId);
				txt1 = ele_txt.innerHTML; // cell[ index 5] = text 	; 
				txt2 = ele_tts.innerHTML; // text to speak				
				
				//console.log("??anto txt1=", txt1,  "   txt2=", txt2);  
				
				tts_3_boldCell(tr1, this1, 0, "onclick_tts_playSynthVoice_row");
				
		 }  else {
			    txt1 = ele_orig_line1.innerHTML;
				txt2 = ele_tts_line1.innerHTML;
		 } 
	     var txt3;
	     if ((txt2 == "") || (txt2 == "undefined"))  txt3 = txt1;
	     else txt3 = txt2;
		 
		 if (swPause) {		
			var ww1 =  (txt3+" ").replaceAll("–"," ").replaceAll("-"," ").
					replaceAll(", "," ").replaceAll(" ."," ").replaceAll(". "," ").replaceAll("..."," ").
					replaceAll("? "," ").replaceAll("! "," ").split(" "); 
			txt3 = "";
			for(var g=0; g < ww1.length; g++) {	
				var ww2 = ww1[g].trim(); 
				if (ww2 != "") txt3 += ww2 + ". "; 
			} 
		 }		 
	    //console.log("4 onclick_tts_playSynthVoice_row2()  txt3="  + txt3 ); 	
		
		onclick_tts_text_to_speech2(txt3, 3);
		 
 } // end of onclick_tts_playSynthVoice_row
 

//-------------------------------------------------- 

function onclick_tts_playSynthVoice_m1_row2(this1, ixTD, swPause,swNewVoice) {

	//call_boldCell_ix(this1, ixVoice, "TTS_onclick_tts_ClipSub_Play3");

	var begix, endix; 
	[begix, endix] = fromIxToIxLimit;	
	
	var id_pref = "idc_" ;
	//------------	
	var id_pref_sp = id_pref; 
	var id_pref_idb = id_pref.replace("idc","idb");  
	tts_3_showHide_if_book_opened_from_to(id_pref, id_pref_idb, begix, endix); 
	
	if (id_pref=="widc_") {
		id_pref_sp = "widtts_";
	} {
		if (id_pref == "idc_")  id_pref_sp = "idtts";  
	}
	
	TTS_LOOP_begix=begix;
	TTS_LOOP_endix=endix; 
	TTS_LOOP_swLoop=false; 	
	
    var txt3 = "";
    for (var t1 = begix; t1 <= endix; t1++) {
		var txtO = document.getElementById(id_pref + t1).innerHTML;
        var txtSp = document.getElementById(id_pref_sp + t1).innerHTML.trim();
		if (txtSp == "") {
			txtSp = txtO.trim(); 
		}
        txt3 += txtSp + " ";  // separatore di parole = " "    
    }
		   
		 if (swPause) {		
			var ww1 =  (txt3+" ").replaceAll("–"," ").replaceAll("-"," ").
					replaceAll(", "," ").replaceAll(" ."," ").replaceAll(". "," ").replaceAll("..."," ").
					replaceAll("? "," ").replaceAll("! "," ").split(" "); 
			txt3 = "";
			for(var g=0; g < ww1.length; g++) {	
				var ww2 = ww1[g].trim(); 
				if (ww2 != "") txt3 += ww2 + ". "; 
			} 
		 }
		 
		if (swNewVoice) {
			lastNumVoice++; 
			if (lastNumVoice >= totNumMyLangVoices) lastNumVoice = 0; // to change voice on each cycle
		} else {
			lastNumVoice = 0; 
		}
	
    onclick_tts_text_to_speech2(txt3, 5);  	

} // end of onclick_tts_playSynthVoice_m1_row2()

//------------------------------------------

function onclick_tts_playSynthVoice_m1_row3(this1, ixTD, swPause,swNewVoice) {
	var begix, endix; 
	
	var td1 = this1.parentElement;
	var tr1 = td1.parentElement;

	var id_tr0 = tr1.id.split("_");
	var numId = parseInt(id_tr0[1]); 	
	var pre_idtr= id_tr0[0]; 
	
	
	//call_boldCell_ix(this1, ixVoice, "TTS_onclick_tts_ClipSub_Play3");

	var pre_idtr1 = pre_idtr.substr(0,1); 	

	if (pre_idtr1 == "w") {
		[begix, endix] = word_fromIxToIxLimit
	} else {
		pre_idtr1 = ""; 
		[begix, endix] = fromIxToIxLimit;	
	}

	var txt1 = "",
	txt2 = "";

	var id_pref     = pre_idtr1 + "idc_"  ;
	var id_pref_idb = pre_idtr1 + "idb_"  ;  
	var id_pref_sp  = pre_idtr1 + "idtts_";
	
	//tts_3_showHide_if_book_opened_from_to(id_pref, id_pref_idb, begix, endix); 

	
	TTS_LOOP_begix=begix;
	TTS_LOOP_endix=endix; 
	TTS_LOOP_swLoop=false; 	
	
	var txt3 = "";
    for (var t1 = begix; t1 <= endix; t1++) {
		var txtO  = document.getElementById(id_pref    + t1).innerHTML;
        var txtSp = document.getElementById(id_pref_sp + t1).innerHTML.trim();
		if (txtSp == "") {
			txtSp = txtO.trim(); 
		}
        txt3 += txtSp + " ";  // separatore di parole = " "    
    }

	if (swPause) {		
		var ww1 =  (txt3+" ").replaceAll("–"," ").replaceAll("-"," ").
		replaceAll(", "," ").replaceAll(" ."," ").replaceAll(". "," ").replaceAll("..."," ").
		replaceAll("? "," ").replaceAll("! "," ").split(" "); 
		txt3 = "";
		for(var g=0; g < ww1.length; g++) {	
			var ww2 = ww1[g].trim(); 
			if (ww2 != "") 
				txt3 += ww2 + ". "; 
		} 
	}

	if (swNewVoice) {
		lastNumVoice++; 
		if (lastNumVoice >= totNumMyLangVoices) 
			lastNumVoice = 0; // to change voice on each cycle
	} else {
		lastNumVoice = 0; 
	}

	onclick_tts_text_to_speech2(txt3, 6);  	

} // end of onclick_tts_playSynthVoice_m1_row3()

//--------------------------------

function onclick_tts_playSynthVoice_word3(this1, ixTD123, swPause,swNewVoice) {

	if (tts_3_play_or_cancel(this1) < 0) {
		return;
	}	
    if (swNewVoice) {
		lastNumVoice++; 
		if (lastNumVoice >= totNumMyLangVoices) 
			lastNumVoice = 0; // to change voice on each cycle
	} else {
		lastNumVoice = 0; 
	}	

	var td1 = this1.parentElement;
	var tr1 = td1.parentElement;

	var txt1 = "",
	txt2 = "";

	var id_tr0 = tr1.id.split("_");
	var numId = parseInt(id_tr0[1]); 	
	var pre_idtr= id_tr0[0]; 
	var pre_idtr1 = pre_idtr.substr(0,1); 
	
	if (pre_idtr1 != "w") pre_idtr1 = "";
	
	var ele_txt = document.getElementById(pre_idtr1 + "idc_"+ numId); 
	
	if (ele_txt == null) return;
	
	var ele_tts = document.getElementById(pre_idtr1 + "idtts_" + numId);
	

	txt1 = ele_txt.innerHTML; // cell[ index 5] = text 	; 
	txt2 = ele_tts.innerHTML; // text to speak


	var txt3;
	if (txt2 == "") txt3 = txt1;
	else txt3 = txt2;

	if (swPause) {	
		txt3 = tts_3_breakTextToPause(txt3, pre_idtr1 ); 
	}
	
	onclick_tts_text_to_speech2(txt3, 7);
		 
 } // end of onclick_tts_playSynthVoice_word3

//-------------------------------------------------


function onclick_tts_text_to_speech2(txt1, wh) {	
	//console.log( "onclick_tts_text_to_speech2(", txt1 , ")" )
	sw_pause = false; 	
	startTime = new Date();	
	txt_length = txt1.length; 
	
	utteranceList = []; 
	x1_line=0; 
	txt1 = tts_3_removeBold_and_Font(txt1); 
    
	var newLine = tts_3_break_text(txt1, TXT_SPEECH_LENGTH_LIMIT, false);  // 3rd param true =  sw_hold_existing_endOfLine

	newLine = newLine.replaceAll("\n","\n\n");
	
    textLines = newLine.split("\n");
	
    var objtxt_to_speak;
    //var riga;
	//------------
    for (var v1 = 0; v1 < textLines.length; v1++) {		
		objtxt_to_speak = new SpeechSynthesisUtterance( textLines[v1]);		
        utteranceList.push(objtxt_to_speak);
    }
    objtxt_to_speak = utteranceList[0];
	
	//speech = objtxt_to_speak; // 1
  
	objtxt_to_speak.onend = tts_3_speech_end_fun;
	

	
	tts_3_speak_a_line(objtxt_to_speak,"1." + wh);	
	

} // end of onclick_tts_text_to_speech2() 	
//----------------------------------




//------------------------------------------------

function onclick_tts_change_voice(this1) {
	
    var vindex = this1.value;
	voice_toUpdate_speech = voiceList[vindex];	
	
	
	LS_voice_index = vindex; 	
	
	fun_set_localStorage_item_from_vars(); 	
	
    console.log("XXXX  voice: " + 
		" index=" + LS_voice_index +
		 " lang=" + voice_toUpdate_speech.lang +
		 " name=" + voice_toUpdate_speech.name ); 
	
} // end of  onclick_tts_change_voice(); 

//-------------------------------------------------

	
         function onclick_tts_changeRate(this1) {
			var rate = parseFloat(this1.value);
			if (rate < 0.30) rate = 0.30; 
			last_rate = rate; 
			this1.value = rate; 
			speech_rate = rate; 
			if (last_objtxt_to_speak) last_objtxt_to_speak.rate = rate; 
			var thisTD = this1.parentElement; 
			var preTD  = thisTD.parentElement.children[1]; 
			preTD.innerHTML = rate;  
         }
         //---------------------------------------
         function onclick_tts_changePitch(this1) {
         	var pitch = this1.value;
			if (pitch < 0.1) pitch = 0.1; 
			this1.value  = pitch;
         	speech_pitch = pitch;			
			if (last_objtxt_to_speak) last_objtxt_to_speak.rate = pitch; 
			var thisTD = this1.parentElement; 
			var preTD  = thisTD.parentElement.children[1]; 
			preTD.innerHTML = pitch;  
         } 
         //----------------------------------
		function onclick_tts_speech_pause() {
			//console.log("pause"); 
			if (synth.speaking) { 
				sw_pause = true; 
				synth.pause(); 
			}
		}
		//---------------------
		function onclick_tts_speech_resume() {
			//console.log("resume"); 
			sw_pause = false; 
			window.speechSynthesis.resume();
			synth.resume(); 
		}
				 
		 //----------------------
		 
         function onclick_tts_speech_cancel() {
			//console.log("*** cancel ***"); 
			sw_cancel = true; 
			if (synth.speaking) { 
				synth.cancel();
			}
         }                                                                       
         //------------------------------------

function onclick_tts_change_synth_rate(this1) {
	speech_rate = parseFloat(this1.value);
	if (speech_rate < 0.25) { 
		speech_rate = 0.25; 
	}
	document.getElementById("id_syncRate1").value = speech_rate;
	document.getElementById("id_setSpeedy").value = speech_rate;
}

//------------------------------------------------------

function TOGLIonclick_tts_seeWords(this1, numId) {	
	
	var anal_txt = ""; var anal_tts_txt=""; 
	var idc1 = "idc_"  + numId;
	var idtts= "idtts" + numId; 

	var anal_ele_idc   = document.getElementById(idc1 );		
	var anal_ele_idtts = document.getElementById(idtts);	
		
	if (anal_ele_idc) {
		anal_txt = anal_ele_idc.innerHTML;
		anal_tts_txt= anal_ele_idtts.innerHTML; 
	} else {
		return;
	}
	
	var eleTR = anal_ele_idtts.parentElement.parentElement.parentElement; 
	var trHeight = eleTR.offsetHeight; 	
	
	var id_analWords = "idw_" + numId;
	var ele_wordset = document.getElementById(id_analWords);   
	
	
	if (last_ele_analWords_id != "") {	
		// remove the previous 
		var last_ele_analWords = document.getElementById(last_ele_analWords_id);
		if (last_ele_analWords)  {
			
					
			last_ele_analWords.style.height = null;   				
			last_ele_analWords.innerHTML = "";  
			last_ele_analWords_tr.style.height = last_ele_analWords_height;	
			
				
			last_ele_analWords = null; 					
		}	
		if (id_analWords == last_ele_analWords_id) {  // if it's the same as the previous then  remove it  		
			last_ele_analWords = null; 	
			last_ele_analWords_id = "";
			return; 
		}	
		last_ele_analWords_id = "";
	}	
	
	var table_txt = tts_3_spezzaRiga2(anal_txt, anal_tts_txt)	 ;   
 	
	var divWord = "";
	
	divWord += table_txt;
	
	ele_wordset.innerHTML = divWord; 
	
	var prevTR  = document.getElementById( "idtr_" + (numId-4) ); 
	if (prevTR) tts_5_fun_scroll_tr_toTop( prevTR ); 	// scroll 
		
	last_ele_analWords_id = id_analWords;
	last_ele_analWords_tr = eleTR; 
	last_ele_analWords_height = trHeight;  
			
} //  end of onclick_tts_seeWords()
	
//-------------------------------------

//-------------------------
function onclick_tts_text_to_speech_ix(id_pref, ixWord, swLoop, this1) {
	
	var ele1 = document.getElementById(id_pref + ixWord);
	var txt1; 
	if (ele1) { 
		txt1 = ele1.innerHTML;
	} else { 
		return; 
	} 
	var tts_txt1 = txt1; 
	//  id="widc_4">coeli</div> <div style="display:none;" id="widtts_4">celi</div>
	
	
	
	if (id_pref=="widc_") {
		var eleTTS = document.getElementById("widtts_" + ixWord);
		if (eleTTS) {
			tts_txt1 = eleTTS.innerHTML;
		}	
	}   
	
	var id_pref_idb = id_pref.replace("idc","idb");  
	
	tts_showHide_if_book_opened(id_pref,id_pref_idb, ixWord) ;
	
	TTS_LOOP_begix   = ixWord;
	TTS_LOOP_endix   = ixWord; 
	TTS_LOOP_swLoop  = swLoop; 	
	TTS_LOOP_elem    = this1;
	
    onclick_tts_text_to_speech2(tts_txt1 ,1 );

} // end of onclick_tts_text_to_speech_ix()

//----------------------------------

function onclick_tts_text_to_speech_from_to(id_pref, begix, endix, swLoop, wh) {
		console.log("??? anto?? file word_cbc....  () " + wh + " (id_pref=" + id_pref + " begix=" + begix + " endix=" + endix);
	console.log("??anto?? word...to_speech.. onclick_tts_text_to_speech_from_to(id_pref=" + id_pref + " begix=" + begix + " endix=" + endix);
	var id_pref_sp = id_pref; 
	var id_pref_idb = id_pref.replace("idc","idb");  
	tts_3_showHide_if_book_opened_from_to(id_pref, id_pref_idb, begix, endix); 
	
	if (id_pref=="widc_") {
		id_pref_sp = "widtts_";
	} {
		if (id_pref == "idc_")  id_pref_sp = "idtts";  
	}
	
	TTS_LOOP_begix=begix;
	TTS_LOOP_endix=endix; 
	TTS_LOOP_swLoop=swLoop; 	
	
    var txt1 = "";
    for (var t1 = begix; t1 <= endix; t1++) {
		var txtO = document.getElementById(id_pref + t1).innerHTML;
        var txtSp = document.getElementById(id_pref_sp + t1).innerHTML.trim();
		if (txtSp == "") {
			txtSp = txtO.trim(); 
		}
		
        txt1 += txtSp + " ";  // separatore di parole = " "    
    }
	console.log("\ttxt1=" + txt1.substring(0,80) + "...");
	
    onclick_tts_text_to_speech2(txt1, 2);  

} // end of onclick_tts_text_to_speech_from_to()

//-------------------------------------------------

function onclick_tts_show_row(this1, z3) {
	tts_5_removeLastBold(); 
	if (this1 == false) { return; }	
	
	if (this1.children[0].style.display == "none") {  // no openbook   
		this1.children[0].style.display = "block";                         // show opened book image  
		this1.children[1].style.display = "none";						  // hide closed book image 	
	} else {
		this1.children[0].style.display = "none";                          //  hide opened book image  
		this1.children[1].style.display = "block";						  //  show closed book image 	
	}
	tts_5_show_hideORIG(z3);
	tts_5_show_hideTRAN(z3);
}	
//-------------------------------------------------------------------------

function onclick_tts_word_show_row(this1, z3, isWord, is_m1) {
	tts_3_word_removeLastBold(isWord); 
	if (this1 == false) { return; }	
	
	if (this1.children[0].style.display == "none") {  // no openbook   
		this1.children[0].style.display = "block";                         // show opened book image  
		this1.children[1].style.display = "none";						  // hide closed book image 	
	} else {
		this1.children[0].style.display = "none";                          //  hide opened book image  
		this1.children[1].style.display = "block";						  //  show closed book image 	
	}
	tts_3_word_show_hideORIG(z3, isWord);
	
}	
//-----------------------------------------------------

//-----------------------------
function onclick_tts_OneClipRow_showHide_sub( thisX, sw_allSel, swAllAll) {
	
	if (thisX == false) { return; }
		

	let id1;
	let inBeg, inEnd; 
	inBeg      = begix;
	inEnd      = endix; 
	if (swAllAll) {
		inBeg= clipFromRow_min;
		inEnd= line_list_o_from1.length-1; 
	}

	
	if (begix > endix) {
		inBeg  = endix;
		inEnd  = begix; 		
	} 
	 
	var style0 , style1; 

	if (swAllAll) {
		if (thisX.children[0].style.display == "block") {  // openbook   
			style0 = "block";                         // show opened book image  
			style1 = "none";						  // hide closed book image 	
		} else {
			style0 = "none";                          //  hide opened book image  
			style1 = "block";						  //  show closed book image 	
		}
	} else {
		tts_5_fun_oneRow00S(); 	
	}
	tts_5_fun_oneRow11S(1); 
	
	if (sw_allSel) {	
		//console.log("    onclick_tts_OneClipRow_showHide_sub()   sw_allSel");
		for(var g=inBeg; g <= inEnd; g++) {
			id1 = "idb_" + g;   			
			thisX = document.getElementById(id1); 
			tts_5_fun_oneRow11S(1+inEnd-inBeg); 	
		} 
	} 	
	//--------------
	function tts_5_fun_oneRow00S() {
		if (thisX == false) { return; }	
		
		if (thisX.children[0].style.display == "none") {  // no openbook   
			style0 = "block";                         // show opened book image  
			style1 = "none";						  // hide closed book image 	
		} else {
			style0 = "none";                          //  hide opened book image  
			style1 = "block";						  //  show closed book image 	
		}
	}	
	//--------------
	function tts_5_fun_oneRow11S(nn) {	
		if (thisX == false) { return; }
		
		thisX.children[0].style.display = style0;         // show/hide  opened book image  
		thisX.children[1].style.display = style1; 		  // show/hide closed book image 
		//let subid = thisX.id.replace("idb","idc"); // testo normale 
		let subid = thisX.id.replace("idb","idp");    // testo con parola evidenziata
		//console.log("subid=" + subid + " last2="  + subid.substring( subid.length-2)  ); 
		
		if (subid.substring( subid.length-2) == "_m") {
			return; 
		} 
		let ele1 = document.getElementById( subid );
		
		//console.log(" fun_fun_fun_oneRow11()  subid=" + subid + " ele1.id=" + ele1.id + " style0=" + style0 +" thisX.outer=" + thisX.outerHTML  )  
		
		if (style0 == "block") {
			//console.log("   onclick_tts_OneClipRow_showHide_sub()  " + subid + "  visibile");
			//ele1.style.color = null; // style.color is set only when equal to background color 
			tts_5_fun_makeTextVisible(ele1);  
		} else {
			//console.log("   onclick_tts_OneClipRow_showHide_sub() " + subid + " INVISIBILE");
			tts_5_fun_makeTextInvisible(ele1); 
		}
	}
	
} // end of onclick_tts_OneClipRow_showHide_sub()

//-----------------------------------------

function onclick_tts_OneClipRow_showHide_tran( thisX, sw_allSel ) {
	if (thisX == false) { return; }
	
	let tran_id = thisX.id.replace("idbT_","idt_"); 

	let id1;
	let inBeg, inEnd; 
	inBeg      = begix;
	inEnd      = endix; 	
	if (begix > endix) {
		inBeg  = endix;
		inEnd  = begix; 		
	} 
	var outDisplay_block ;  
	var style0 , style1; 

	
	fun_fun_oneRow00T(); 	
	
	fun_fun_fun_oneRow11T(false); 
	
	if (sw_allSel) {	
		for(var g=inBeg; g <= inEnd; g++) {
			id1 = "idbT_" + g;  			
			thisX = document.getElementById(id1); 
			//console.log("gruppo tran id1=" + id1 ) ;  
			fun_fun_fun_oneRow11T(true); 	
		} 
	} 
	
	//--------------
	function fun_fun_oneRow00T() {	
		if (thisX == false) { return; }		
		
		if (thisX.children[0].style.display == "none") {  //  opened_translation symbol is hided  (T)  
			//console.log(" tran  mostra T grande style0=block" ); 
			style0 = "block";                         // show opened_translation symbol   (T) 
			style1 = "none";						  // hide closed_translation symbol   (image)				
			outDisplay_block =	"block" ;             // show translation line 			 
			sw_active_show_lastSpokenLineTranslation = true;
		} else {
			//console.log(" tran  mostra t piccolo   style0 = none") ;	
			style0 = "none";                          // hide opened_translation symbol  (T) 
			style1 = "block";						  // show closed_translation symbol  (image) 	
			outDisplay_block =	"none" ;              // hide translation line	
			sw_active_show_lastSpokenLineTranslation = false;	
		}
	}
	//--------------
	function fun_fun_fun_oneRow11T(sw_g) {	
			//console.log( "tran  fun_fun_fun_oneRow11T()  thisX.id=" + thisX.id);  	
			
		if (thisX == null) {  return; }
		if (thisX == false) {   return; }
		
		thisX.children[0].style.display = style0;         // show/hide opened_translation symbol  (T)
		thisX.children[1].style.display = style1; 		  // show/hide closed_translation symbol  (image) 	
		
		tran_id = thisX.id.replace("idbT_","idt_"); 
		if (document.getElementById(tran_id)) {
			document.getElementById(tran_id).style.display = style0;  // show/hide  translation line	
		}
	}

	
} // end of onclick_tts_OneClipRow_showHide_tran()

//----------------------------------------------

//                  
function onclick_tts_word_arrowFromIx(ele_td_arrow, z3, isWord, is_m1) {
    //------------------------------------------
    // button from ( --> ) has been clicked 
    //------------------------------------------
 
    tts_3_word_removeLastBold(isWord);
    tts_3_word_fun_invisible_prev_fromto(-1, isWord, is_m1 );
	if (isWord) {
		word_fromIxToIxLimit = [z3, -1];
		[begix, endix] = word_fromIxToIxLimit; 
		tts_3_word_fun_copy_openClose_to_tr_m1(z3, isWord, is_m1); //  copy open/Close book style from this line idtr_xx to the upper idtr_xx_m1
		word_fromIxToIxButtonElement = [ele_td_arrow, null];
		ele_td_arrow.style.backgroundColor = "green";
	} else {
		fromIxToIxLimit = [z3, -1];
		[begix, endix] = fromIxToIxLimit;
		tts_3_word_fun_copy_openClose_to_tr_m1(z3, isWord, is_m1); //  copy open/Close book style from this line idtr_xx to the upper idtr_xx_m1
		fromIxToIxButtonElement = [ele_td_arrow, null];
		ele_td_arrow.style.backgroundColor = "green";
	}

} // end of onclick_tts_word_arrowFromIx  

//---------------------------------------
function onclick_tts_word_arrowToIx(ele_td_arrow, z3, isWord, is_m1) {
    //------------------------------------------
    // button to( <-- ) has been clicked 
    //------------------------------------------	
    var endix2; var id_post_tr_end_space2;
	var id_pre_tr_beg_space;
	var id_pre_tr_head ;
	var id_post_tr_end_space ;
		
	
	
	if (isWord) {
		//reset previous ..._ToIx  button     
		if (word_fromIxToIxButtonElement[1]) {
			word_fromIxToIxButtonElement[1].style.backgroundColor = null;
			endix2 = word_fromIxToIxLimit[1];
			if (endix2 > 0) {
				id_post_tr_end_space2 = "widtr_" + (endix2 + 1) + "_m2";
				if (document.getElementById(id_post_tr_end_space2)) {
					document.getElementById(id_post_tr_end_space2).style.display = "none";
				}
			}
		}
		//--------- new ... _ToIx ----------------------------------
		if (z3 <= word_fromIxToIxLimit[0]) {
			// this set the arrows 
			var eleFromArrow = word_fromIxToIxButtonElement[0];
			var eleTr = eleFromArrow.parentElement.parentElement; 
			console.log("eleTR " + eleTr.tagName + " id="+ eleTr.id); 
			var preEleTr = eleTr.previousElementSibling;  
			var preEleTr2 = preEleTr.previousElementSibling;  
			console.log("preEleTR " + preEleTr.tagName + " id="+ preEleTr.id); 
			eleFromArrow.style.backgroundColor = null;
			preEleTr.style.display = "none";
			preEleTr2.style.display = "none";
			return; 
		}
		
		word_fromIxToIxLimit[1] = z3;
		word_fromIxToIxButtonElement[1] = ele_td_arrow;
		[begix, endix] = word_fromIxToIxLimit;
		id_pre_tr_beg_space  = "widtr_" + begix + "_m2";
		id_pre_tr_head       = "widtr_" + begix + "_m1";
		id_post_tr_end_space = "widtr_" + (endix + 1) + "_m2";
		tts_3_word_fun_copyHeaderSelected(begix, endix);
	} else {
		//reset previous ..._ToIx  button     
		if (fromIxToIxButtonElement[1]) {
			fromIxToIxButtonElement[1].style.backgroundColor = null;
			endix2 = word_fromIxToIxLimit[1];
			if (endix2 > 0) {
				id_post_tr_end_space2 = ele_tr_idPref + (endix2 + 1) + "_m2";
				if (document.getElementById(id_post_tr_end_space2)) {
					document.getElementById(id_post_tr_end_space2).style.display = "none";
				}
			}
		}
		//--------- new ... _ToIx -----
		fromIxToIxLimit[1] = z3;
		fromIxToIxButtonElement[1] = ele_td_arrow;
		[begix, endix] = word_fromIxToIxLimit;
		id_pre_tr_beg_space = "widtr_" + begix + "_m2";
		id_pre_tr_head = "widtr_" + begix + "_m1";
		id_post_tr_end_space = "widtr_" + (endix + 1) + "_m2";
		fun_copyHeaderSelected(begix, endix);
	}
	
    if (document.getElementById(id_pre_tr_beg_space)) {
        document.getElementById(id_pre_tr_beg_space).style.display = "table-row";
    }   
    if (document.getElementById(id_pre_tr_head)) {
        document.getElementById(id_pre_tr_head).style.display = "table-row";
    }
    if (document.getElementById(id_post_tr_end_space)) {
        document.getElementById(id_post_tr_end_space).style.display = "table-row";
    }   
    ele_td_arrow.style.backgroundColor = "red";
   
} // end of onclick_tts_arrowToIx()

//------------------------------------------

function onclick_tts_word_OneClipRow_showHide_sub( ele_idb, sw_allSel, swAllAll, isWord, is_m1) {	
	
	if (ele_idb == false) { return; }		
	
	//console.log("onclick_tts_word_OneClipRow_showHide_sub() 1 ele_idb ", ele_idb.id); 
	
	let id1;
	let inBeg, inEnd; 
	inBeg      = begix;
	inEnd      = endix; 
	if (isWord == false) { 
		if (swAllAll) {
			inBeg= clipFromRow_min;
			inEnd= line_list_o_from1.length-1; 
		}
	}
	if (begix > endix) {
		inBeg  = endix;
		inEnd  = begix; 		
	} 	 
	var style0 , style1; 	
	if (isWord) {
		word_fun_oneRow00(); 	
	} else {
		if (swAllAll) {
			if (ele_idb.children[0].style.display == "block") {  // openbook   
				style0 = "block";                         // show opened book image  
				style1 = "none";						  // hide closed book image 	
			} else {
				style0 = "none";                          //  hide opened book image  
				style1 = "block";						  //  show closed book image 	
			}
		} else {
			word_fun_oneRow00(); 	
		}
	}
	//console.log("onclick_tts_word_OneClipRow_showHide_sub() 2 ele_idb ", ele_idb.id); 
	word_fun_oneRow22(1); 
	
	if (sw_allSel) {	
		for(var g=inBeg; g <= inEnd; g++) {
			if (isWord) id1 = "widb_" + g;   
			else id1 = "idb_" + g;   			
			ele_idb = document.getElementById(id1); 
			//console.log("onclick_tts_word_OneClipRow_showHide_sub() 2 ", " id1=", id1 ); console.log("\t ele_idb ", ele_idb.id); 
			word_fun_oneRow22(1+inEnd-inBeg); 	
		} 
	} 	
	//--------------
	function word_fun_oneRow00() {
		if (ele_idb == false) { return; }
		
		if (ele_idb.children[0].style.display == "none") {  // no openbook   
			style0 = "block";                         // show opened book image  
			style1 = "none";						  // hide closed book image 	
		} else {
			style0 = "none";                          //  hide opened book image  
			style1 = "block";						  //  show closed book image 	
		}
		
	}	
	//-------------------  
	function word_fun_oneRow22(nn) {	// 2 onclick_tts_word_OneClipRow_showHide_sub
		
		
		if (ele_idb == false) { return; }
		
		ele_idb.children[0].style.display = style0;         // show/hide  opened book image  
		ele_idb.children[1].style.display = style1; 		  // show/hide closed book image 
		let subid = ele_idb.id.replace("idb","idc"); 		
		//if (is_m1) return;  
		let ele_idc = document.getElementById( subid );
		if (style0 == "block") {
			tts_3_word_fun_makeTextVisible(ele_idc);  
		} else {		
			tts_3_word_fun_makeTextInvisible(ele_idc);
		}
	} // end of word_fun_oneRow22()
	//-------------------------
	
} // end of onclick_tts_word_OneClipRow_showHide_sub()  // 2 

//-----------------------------

//--------------------------------------------------------------
function onclick_tts_playSynthVoice_m1_row(this1, numVoice) {
	TTS_onclick_tts_ClipSub_Play3(this1,numVoice) ;
}
//-----------------------------------------------------
function onclick_tts_ClipSub_Play3(this1,numVoice) {
	
	var ixVoice = numVoice - 1;
		
	voice_toUpdate_speech = listVox[ixVoice][1]; 
	
	call_boldCell_ix(this1, ixVoice, "TTS_onclick_tts_ClipSub_Play3");



	var begix, endix; 
	[begix, endix] = fromIxToIxLimit;	
	
	console.log("\t??anto? file ...existing.. file 2 TTS_onclick_tts_ClipSub_Play3() begix=" + begix + " endix=" + endix); 
	
	
	onclick_tts_text_to_speech_from_to("idc_",begix, endix, false, "2 TTS_on...Play3");
	console.log("uscito da onclick_tts_text_to_speech_from_to()"); 
	
} // end of TTS_onclick_tts_ClipSub_Play3()
//------------------------
									  								
function onclick_tts_playSynthVoice_word(	this1, ixWord, numVoice) {
	onclick_tts_word_OneClipRow_play_Loop3( this1, ixWord, false, true, false,numVoice);
}
//---------------------
function onclick_tts_word_OneClipRow_play_Loop3(this1, ixWord, swLoop, isWord, is_m1,numVoice) {
	
	var eleTR = this1.parentElement.parentElement;
	var id_tr = "";
	if (eleTR == "TR") {
		id_tr = eleTR.id; 
	} 
	
	//console.log("script_3  onclick_tts_word_OneClipRow_play_Loop3() ixWord=" + ixWord + " numVoice=" + numVoice  + "   id_tr=" + id_tr); 

	var ixVoice = numVoice-1; 
	if (ixVoice) {
		voice_toUpdate_speech = listVox[ ixVoice ][1]; 
	}
	
	
	call_boldCell_ix(this1, ixVoice, "onclick_tts_word_OneClipRow_play_Loop3");
	
	onclick_tts_text_to_speech_ix("widc_", ixWord, swLoop, this1);
	
} // end of onclick_tts_word_OneClipRow_play_Loop3()	

//----------------------
function onclick_tts_playSynthVoice_m1_word( this1,numVoice) {
		onclick_tts_word_ClipSub_Play3(      this1, false, true, true, numVoice); 
}
//------------------------
function onclick_tts_word_ClipSub_Play3(this1, swLoop, isWord, is_m1, numVoice) {
	var ixVoice = numVoice - 1;
	
	if (ixVoice) {
		voice_toUpdate_speech = listVox[ixVoice][1] ; 
	}
	
    var sw_tts2 = (sw_tts || isWord);  
    var begix, endix;
	if (isWord) {	
		[begix, endix] = word_fromIxToIxLimit;
		if (sw_tts2) { // TTS 
			if (TTS_LOOP_swLoop) {
				TTS_LOOP_swLoop = false;
				return;
			}
			if (word_play_or_cancel(this1) < 0) {
				return;
			}
			onclick_tts_text_to_speech_from_to("widc_", begix, endix, swLoop, "3 word_onclip...Play3");
			return;
		}		
    } else { 	
		[begix, endix] = fromIxToIxLimit;
		if (sw_tts2) { // TTS 
			if (TTS_LOOP_swLoop) {
				TTS_LOOP_swLoop = false;
				return;
			}
			if (word_play_or_cancel(this1) < 0) {
				return;
			}
			onclick_tts_text_to_speech_from_to("idc_", begix, endix, swLoop, "4 word_onclip...Play3");
			return;
		}		
	}

} // end of onclick_tts_word_words1_Play3()

//-------------------------------------------------

function onclick_tts_langSelected() {

	document.getElementById("page0Lang").style.display = "none"; 
	document.getElementById("page0"    ).style.display = "block"; 

} // end of onclick_tts_langSelected()

//-------------------------------------------------

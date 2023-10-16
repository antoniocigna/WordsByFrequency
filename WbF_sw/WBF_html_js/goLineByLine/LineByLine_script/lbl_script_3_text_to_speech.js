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
var currScript = document.currentScript.src;
var bar1 = currScript.lastIndexOf("\\");
var bar2 = currScript.lastIndexOf("/");
//console.log("LOADED file SCRIPT " + currScript.substring(1 + Math.max(bar1, bar2)));
//----------------------------------------------------------------------------------------

let last_objtxt_to_speak;

//=============================================

function tts_3_getUrlData3() {

    console.log("PLAYER  tts_3_getUrlData3() ");

    sw_is_no_videoaudio = true;


    //console.log("\nXXXXXXXXXXXXXXXXXXXXXXXXXX\nX getUrlData3() \nXXXXXXXXXXXXXXXXXXXXXXXXXX\n");

    /**
	document.getElementById("id_voice_language").innerHTML = decodeURI( urlParams.get("p_sel_voicelang" ) );   
	
	var selected_language_fromBuilder = document.getElementById("id_voice_language").innerHTML ; // eg.  en,6
	language_parameters = (selected_language_fromBuilder+",,,").split(",");  
    selected_lang_id = (language_parameters[0]+"   ").trim().substr(0,2); 
	selected_numVoices = parseInt("0" + language_parameters[1].trim() )  ; 	
	if (selected_numVoices > maxNumVoices)  selected_numVoices = maxNumVoices;
	***/


    sw_is_no_videoaudio = true;


    sw_is_no_videoaudio = true;

    cbc_LOCALSTOR_key = "ClipByClip_player_" + encodeURI(title1);


    tts_3_FAKE_onloaded_fun();

} // end of f3_tts_getUrlData3()

//---------------------------------------------
function tts_3_word_build_td_voices() {
    var selected_numVoices2 = 1; // selected_numVoices; // 1;
    var str1 = "";


    var fun1_m1 = '"onclick_tts_playSynthVoice_m1_word(this,';


    var fun2 = '"onclick_tts_word_playSynthVoice_row2(this1, §1§,'; //   continue -->   swLoop, isWord, is_m1,swNewVoice) {


    var oneVoice1_1 = '\n<td class="c_voice" style="';
    var oneVoice1_2 = 'background-color:lightblue;';
    var oneVoice1_31_m1 = '"  ><button class="buttonWhite" onclick=' + fun1_m1;
    var oneVoice1_32 = '"  ><button class="buttonWhite" onclick=' + fun2;

    var oneVoice1_4 = ')">';
    var oneVoice2 = `
		<span style="font-size:2em;height:1.4em;">${speakinghead_symb}</span></button></td>
				`; // do not replace backtick(` `) with quote(") or single_quotation_mark (')
    str1 = "";
    var n;
    var swB = false;


    var str_m2 = "";
    var str_m1 = "";
    for (n = 1; n <= selected_numVoices2; n++) {
        if (swB) {
            swB = false;
            str_m1 += oneVoice1_1.replace("c_voice", "c_voice_m1") + oneVoice1_31_m1 + n +
                oneVoice1_4 + n + oneVoice2.trim();
        } else {
            swB = true;
            str_m1 += oneVoice1_1.replace("c_voice", "c_voice_m1") + oneVoice1_2 + oneVoice1_31_m1 + n +
                oneVoice1_4 + n + oneVoice2.trim();
            //document.getElementById("hvox" + n).style.backgroundColor = "lightblue" ;
        }
        //document.getElementById("hvox" + n).style.fontSize = "0.5em"; 
        str_m2 += "<td></td>";
    }

    var str2 = "";
    for (n = 1; n <= selected_numVoices2; n++) {
        if (swB) {
            swB = false;
            str2 += oneVoice1_1 + oneVoice1_32 + n + oneVoice1_4 + n + oneVoice2.trim();
        } else {
            swB = true;
            str2 += oneVoice1_1 + oneVoice1_2 + oneVoice1_32 + n + oneVoice1_4 + n + oneVoice2.trim();
            //document.getElementById("hvox" + n).style.backgroundColor = "lightblue" ;
        }
        //document.getElementById("hvox" + n).style.fontSize = "0.5em"; 
    }

    //document.getElementById("col_voce1").span = selected_numVoices; 
    /**
    for(n=selected_numVoices+1; n <=6; n++) {  // all of them are defined as display table-column 
    	document.getElementById("hvox" + n).style.display="none"; 
    }
    **/

    //str1 =  voice_col_tr_td;


    return [str_m2, str_m1, str2];

} // end of word_build_td_voices()


// ===================================================================
function tts_3_spezzaRiga2(orig_riga, tts_riga) {



    var endix2 = -1;



    var orig_riga2 = orig_riga.replaceAll(". ", ". §").replaceAll("! ", "! §").replaceAll("? ", "? §").replaceAll("; ", "; §").
    replaceAll(": ", ": §").replaceAll(", ", ", §").replaceAll(" ", " §");

    if (tts_riga == "") tts_riga = orig_riga;

    var tts_riga2 = tts_riga.replaceAll(". ", ". §").replaceAll("! ", "! §").replaceAll("? ", "? §").replaceAll("; ", "; §").
    replaceAll(": ", ": §").replaceAll(", ", ", §").replaceAll(" ", " §");

    //console.log("\tspezzaRiga2( orig_riga=" + orig_riga + "\n\t\ttts_riga=" + tts_riga); 

    var listaParole = [];
    var listaParo_tts = [];
    var list1 = orig_riga2.split("§");
    var list2 = tts_riga2.split("§");

    //console.log( list1.length + " " + list2.length); 


    if (list2.length != list1.length) list2 = orig_riga2.split("§");

    for (var f = 0; f < list1.length; f++) {
        if (list1[f].trim() != "") {
            listaParole.push(list1[f]);
            listaParo_tts.push(list2[f]);
        }
    }


    var parola1, paro_tts;

    var frase_showTxt = '<table style="border:0px solid red;width:100%;margin-top:1em;"> \n';
    /**
    var optionRatePitch = `
    				<table style="font-size:0.5em;">         		
    			 <tr>
    				<td id="id_905" style="width:2em;padding:0;">§rate§</td>
    				<td style="width:0.5em;padding:0;">1</td>
    				<td style="width:0.5em;padding:0;">
    				<input  id="id_rate" type="range" min="0.0" max="2" value="1" step="0.5" oninput="onclick_tts_changeRate(this)">
    				</td>				
    			 </tr>
    		</table>
    			` ;//  	
    optionRatePitch = optionRatePitch.replace("§rate§", document.getElementById("m105").innerHTML); 
    ***
	
    frase_showTxt += '<tr>'  + '<td></td><td></td><td></td><td>' +
    		 '<td colspan="' +listaParole.length + '">' + 
    		 optionRatePitch +			 
    		 '</td><td></td></tr>\n'; 
	
    ****
     id="widc_§1§">§4txt§</div>	
     id="widtts_§1§">§ttsWtxt§</div>	
    ***	
	
    ***/
    endix2 = listaParole.length;

    for (let z3 = 0; z3 < listaParole.length; z3++) {
        parola1 = listaParole[z3];
        paro_tts = listaParo_tts[z3];
        let rowclip = word_tr_allclip.replaceAll("§1§", z3).replaceAll("§4txt§", parola1).replaceAll("§ttsWtxt§", paro_tts);
        frase_showTxt += rowclip + "\n";
    } // end of for z3

    return frase_showTxt += '</table>\n';

} //  end of  spezzaRiga2()

//------------------------------------------

function tts_3_word_show_hideORIG(z3, isWord) {
    if (isWord) {
        let ele_orig_toTestShow = document.getElementById("widb_" + z3); // onclick ...  children opened/closed orig.image  (book) 		
        let ele_orig_text = document.getElementById("widc_" + z3); // element of original text to show/hide	 
		let ele_orig_textTRA = document.getElementById("widcT_" + z3); // translation 
		
		//console.log("ele_orig_text =" + ele_orig_text.id  + " outer = " + ele_orig_text.outerHTML, "\n\tele_orig_textTRA=" + ele_orig_textTRA.id  + " outer = " + ele_orig_textTRA.outerHTML );  
		
        // show subtitle if icon opened book is visible otherwise hide it ( icon closed book is visible) 
        tts_3_word_fun_oneClipRow_showHide_ORIG_if_book_opened(ele_orig_text, ele_orig_toTestShow, z3, isWord);
		tts_3_word_fun_oneClipRow_showHide_ORIG_if_book_opened(ele_orig_textTRA, ele_orig_toTestShow, z3, isWord);
		
		//console.log("ele_orig_textTRA =" + ele_orig_textTRA .id + " inner = " + ele_orig_textTRA.outerHTML);  
		
		
    } else {
        let ele_orig_toTestShow = document.getElementById("idb_" + z3); // onclick ...  children opened/closed orig.image  (book) 		
        let ele_orig_text = document.getElementById("idc_" + z3); // element of original text to show/hide	  
        // show subtitle if icon opened book is visible otherwise hide it ( icon closed book is visible) 
        tts_3_word_fun_oneClipRow_showHide_ORIG_if_book_opened(ele_orig_text, ele_orig_toTestShow, z3, isWord);
    }
	
	
} // end of  word_show_hideORIG

//-------------------------

function tts_3_call_boldCell_ix(this1, ixVoice, wh) {
    var td1 = this1.parentElement;
    var tr1 = td1.parentElement;
    tts_3_boldCell(tr1, this1, ixVoice, " call_boldCell_ix() " + wh);
}
//-------------------------------------

function tts_3_show_speakingVoiceFromVoiceLangName(voice_lang, voice_name) {

    var msg1 = document.getElementById("m120").innerHTML; //  spoken in
    var lang0 = get_languageName(voice_lang).split("-");

    var msg = "<b>" + lang0[0] + "</b><br><small>" +
        document.getElementById("m120").innerHTML + //  spoken in
        "</small><br><b>" + lang0[1] + "</b><br>";

    ele_voxLangDisplay.innerHTML = msg + "<br><small>" + voice_name + "</small>";

} // 

//-------------
function tts_3_show_speakingVoice(objtxt_to_speak) {
    tts_3_show_speakingVoiceFromVoiceLangName(objtxt_to_speak.voice.lang, objtxt_to_speak.voice.name);
} // 

//------------------------------------
function tts_3_set_speech_Parms(objtxt_to_speak) {

	//console.log("tts_3_set_speech_Parms() lastNumVoice=" + lastNumVoice + " lang=" + listVox[lastNumVoice][0]);
	var myVoice = listVox[lastNumVoice][1];
	var voice_lang2 = myVoice.lang.substr(0,2); 
	
	//voice_lang2 = "mioerrore"; // forzo errore per testare
	
	if (voice_lang2 != selected_voiceLang2) {		
		console.log("error: voice to set (" + myVoice.name + " is not of the selected language (" +  voice_lang2 + " vs " + selected_voiceLang2); 
		console.log("lastNumVoice=" + lastNumVoice  + " listVox.length=" + listVox.length); 
		//console.log(signalerror); 
		tts_2_fill_the_voices(); 
		if (lastNumVoice >= listVox.length) lastNumVoice = 0;  
		myVoice = listVox[lastNumVoice][1];
	}
	
    last_objtxt_to_speak = objtxt_to_speak;
	
    objtxt_to_speak.voice = myVoice;

    tts_3_show_speakingVoice(objtxt_to_speak);

    objtxt_to_speak.rate = speech_rate;
    objtxt_to_speak.pitch = speech_pitch;


} // tts_3_set_speech_Parms()

//---------------------------------------
function tts_3_word_fun_invisible_prev_fromto(interX, isWord, is_m1) {
    // eliminate bold of the  previous group of lines, unless this is a line in them  

    var id_pre_tr_beg_space, id_pre_tr_head, id_post_tr_end_space;
    if (isWord) {
        [begix, endix] = word_fromIxToIxLimit; // previously set 
        if ((interX >= begix) && (interX <= endix)) return;
        id_pre_tr_beg_space = "widtr_" + begix + "_m2";
        id_pre_tr_head = "widtr_" + begix + "_m1";
        id_post_tr_end_space = "widtr_" + (endix + 1) + "_m2";
        if (word_fromIxToIxButtonElement[0]) {
            word_fromIxToIxButtonElement[0].style.backgroundColor = null;
            if (document.getElementById(id_pre_tr_beg_space)) {
                document.getElementById(id_pre_tr_beg_space).style.display = "none";
            }
            if (document.getElementById(id_pre_tr_head)) {
                document.getElementById(id_pre_tr_head).style.display = "none";
            }
        }
        if (word_fromIxToIxButtonElement[1]) {
            word_fromIxToIxButtonElement[1].style.backgroundColor = null;
            if (document.getElementById(id_post_tr_end_space)) {
                document.getElementById(id_post_tr_end_space).style.display = "none";
            }
        }
    } else {
        [begix, endix] = fromIxToIxLimit;
        if ((interX >= begix) && (interX <= endix)) return;
        id_pre_tr_beg_space = "idtr_" + begix + "_m2";
        id_pre_tr_head = "idtr_" + begix + "_m1";
        id_post_tr_end_space = "idtr_" + (endix + 1) + "_m2";
        if (fromIxToIxButtonElement[0]) {
            fromIxToIxButtonElement[0].style.backgroundColor = null;
            if (document.getElementById(id_pre_tr_beg_space)) {
                document.getElementById(id_pre_tr_beg_space).style.display = "none";
            }
            if (document.getElementById(id_pre_tr_head)) {
                document.getElementById(id_pre_tr_head).style.display = "none";
            }
        }
        if (fromIxToIxButtonElement[1]) {
            fromIxToIxButtonElement[1].style.backgroundColor = null;
            if (document.getElementById(id_post_tr_end_space)) {
                document.getElementById(id_post_tr_end_space).style.display = "none";
            }
        }
    }
} // end of word_fun_invisible_prev_fromto()




//------------------------------------------

function tts_3_word_fun_copy_openClose_to_tr_m1(z3, isWord, is_m1) {
    var i_eleSubO, o_eleSubO;
    if (isWord) {
        i_eleSubO = document.getElementById("widb_" + z3);
        o_eleSubO = document.getElementById("widb_" + z3 + "_m");
    } else {
        i_eleSubO = document.getElementById("idb_" + z3);
        o_eleSubO = document.getElementById("idb_" + z3 + "_m");
    }
    try {
        o_eleSubO.children[0].style.display = i_eleSubO.children[0].style.display; // ${openbook_symb}
        o_eleSubO.children[1].style.display = i_eleSubO.children[1].style.display; // ${closedbook_symb}
    } catch (e1) {
        console.log("error in 'word_fun_copy_openClose_to_tr_m1(z3=" + z3 + ")'");
        console.log(e1);
    }
} // end of word_fun_copy_openClose_to_tr_m1() 
//---------------------------------------


//-----------------------------------------------
function tts_3_word_fun_copyHeaderSelected(begix, endix) {

    let id1;
    let inBeg, inEnd;

    id1 = "widb_" + begix + "_m";
    var ele_idb = document.getElementById(id1);
    if (ele_idb == false) {
        return;
    }

    inBeg = begix;
    inEnd = endix;
    if (begix > endix) {
        inBeg = endix;
        inEnd = begix;
    }
    var style0, style1;

    tts_3_fun_oneRowZZ1();

    for (var g = inBeg; g <= inEnd; g++) {
        id1 = "widb_" + g;
        ele_idb = document.getElementById(id1);
        tts_3_word_fun_oneRow11(ele_idb);
    }

    //--------------
    function tts_3_fun_oneRowZZ1() {
        if (ele_idb == false) {
            return;
        }
        if (ele_idb.children[0].style.display == "none") { // no openbook   
            style0 = "none"; //  hide opened book image  
            style1 = "block"; //  show closed book image 
        } else {
            style0 = "block"; // show opened book image  
            style1 = "none"; // hide closed book image 	
        }
    }
    //--------------
    function tts_3_word_fun_oneRow11(ele_idb) {
        if (ele_idb == false) {
            return;
        }
        ele_idb.children[0].style.display = style0; // show/hide opened book image  
        ele_idb.children[1].style.display = style1; // show/hide closed book image 
        let subid_idc = ele_idb.id.replace("idb", "idc");
        if (subid_idc.substring(subid_idc.length - 2) == "_m") {
            return;
        }
        let ele_idc = document.getElementById(subid_idc);
        if (ele_idc == false) return;
        if (style0 == "block") {
            tts_3_word_fun_makeTextVisible(ele_idc);
        } else {
            tts_3_word_fun_makeTextInvisible(ele_idc);
        }
    } // end of tts_3_word_fun_oneRow11) //  
    //--------------

} // end of word_fun_copyHeaderSelected()

//-----------------------------
//--------------
function tts_3_word_play_or_cancel(this1) {

    this1.style.backgroundColor = "red";
    ele_last_play = this1;
    return 0;
} // end of  word_play_or_cancel

//----------------------------

function tts_3_word_fun_makeTextInvisible(element) {
    if (element == null) {
        return;
    }
    //element.style.visibility = "hidden"; 
    element.style.display = "none";	
	
	let id1 = element.id
	if (id1.indexOf("widc_") < 0) return;
	let id2 = id1.replace("widc_", "widcT_");
	document.getElementById(id2).style.display = "none";	
	
}
//----------------------------

function tts_3_word_fun_makeTextVisible(element) {
    if (element == null) {
        return;
    }
    element.style.display = "block";
	
	let id1 = element.id
	if (id1.indexOf("widc_") < 0) return;
	let id2 = id1.replace("widc_", "widcT_");
	document.getElementById(id2).style.display = "block";	
	
}

//------------------------
function tts_3_word_removeLastBold(isWord) {

    var id_pref = "idc_";
    if (isWord) id_pref = "widc_";

    if (word_last_BoldRow) {
        word_last_BoldRow.classList.remove("boldLine");
        word_last_BoldRow.style.backgroundColor = null;
        word_last_BoldRow.parentElement.style.border = null;
        var last_ele1_tr = word_last_BoldRow.parentElement.parentElement;
        last_ele1_tr.style.backgroundColor = "lightgrey";
    }
    if (sw_tts2) tts_remove_last_bold(id_pref, isWord);
}
//-------------------------------------------

function tts_3_word_fun_oneClipRow_showHide_ORIG_if_book_opened(ele1, ele_to_test, z3, isWord) {

    var ele1_tr = ele1.parentElement.parentElement;


    tts_3_word_removeLastBold(isWord);
    if (ele1 == null) {
        return;
    }
    if (isWord) word_last_BoldRow = ele1;
    else word_last_BoldRow = ele1;

    if (ele_to_test.children[0].style.display == "block") { // openbook ==> show 
        //ele1.style.visibility = "visible"; 
        ele1.style.display = "block";
        ele1.classList.add("boldLine");
        ele1.style.backgroundColor = "yellow";
        ele1.parentElement.style.border = null;
        //feb if (sw_is_no_videoaudio == false) ele1_tr.style.backgroundColor = "yellow";			
        ele1_tr.style.backgroundColor = "yellow"; //feb 		
    } else { // closebook  ==> hide 
        //ele1.style.visibility = "hidden"; 	
        ele1.style.display = "none";
        ele1.classList.remove("boldLine");
        ele1.style.backgroundColor = null;
        ele1.parentElement.style.border = "1px solid red";
        //feb if (sw_is_no_videoaudio == false) ele1_tr.style.backgroundColor = "yellow";		
        //ele1_tr.style.backgroundColor = "yellow";	//feb	  
    }

} // end of fun_oneClipRow_showHide_ORIG_if_book_opened()
//================================================================	

//js2___________________
//-----------------------------------------------
function tts_3_removeLastEle(id1) {
    //console.log("\tremoveLastEle(id1=" + id1);
    if (document.getElementById(id1)) document.getElementById(id1).remove();
}




//js3_____________________________
//----------------------------------------------------------
function tts_3_break_priority(txt1, maxLen, sw_let_old_newline) {

    if (sw_let_old_newline == false) {
        txt1 = txt1.replaceAll("\n", " "); // eliminate existing newline  
    }

    // break text into lines always for: end of sentence (.), question mark(?), exclamation(!), semicolon(;)  

    var row1 = txt1.replaceAll("<br>", "\n").
    replaceAll(". ", ".\n").
    replaceAll("? ", "?\n").
    replaceAll("! ", "!\n").
    replaceAll("; ", ";\n");

    return row1.split("\n");
} // end of tts_3_break_priority

//-----------------------------------------

function tts_3_break_text(txt1, maxLen, sw_let_old_newline) {

    // break for: new line, end of sentence (.), exclamantion(!)  and question mark(?), and semicolon(";")     
    // break for too long line ( last comma or last blank before reaching the maximum length   

    var rtxt2 = tts_3_break_priority(txt1, maxLen, sw_let_old_newline);

    //console.log("break_text(txt1=" + txt1 + " \n\trtxt2=" + rtxt2);   

    //-------------------------------	
    function tts_3_tooLongLine(oneLine) {
        // break in strings with their length not > maxlen  ( firstly try to find colon(:), then comma(,) and lastily space(" ")  
        var txt3 = oneLine.trim();
        var newLine2 = "";
        var len1;
        var txt3a;
        var u, u1, u2;
        //-------------
        for (var h = 0; h < txt3.length; h++) {
            len1 = txt3.length;
            if (len1 < 1) {
                break;
            }
            if (len1 <= maxLen) {
                newLine2 += txt3 + "\n";
                break;
            }

            txt3a = txt3.substring(0, maxLen);
            u1 = txt3a.lastIndexOf(": ");
            u2 = txt3a.lastIndexOf(", ");
            u = Math.max(u1, u2);
            if (u >= 0) {
                u++;
            } else {
                u = txt3a.lastIndexOf(" ");
            }
            if (u < 0) {
                u = txt3.indexOf(" "); // find next forward 
                if (u < 0) {
                    u = txt3.length; // take all string 
                }
            }
            newLine2 += txt3.substring(0, u) + "\n";

            txt3 = txt3.substring(u).trim();
        }
        return newLine2;

    } // end of tooLongLine();

    //-------------------------------------------

    var newLine = "";
    for (var g = 0; g < rtxt2.length; g++) {
        newLine += tts_3_tooLongLine(rtxt2[g]);
    }


    return newLine;

} // end of break_text() 

//-----------------------------------------
function tts_3_test_break_text(txt1) {

    console.log("old=" + "\n" + txt1 + "\n-------------------\n");

    var newLine = break_text(txt1, TXT_SPEECH_LENGTH_LIMIT, sw_let_old_newline);
    var lines = newLine.split("\n");
    for (var v1 = 0; v1 < lines.length; v1++) {
        console.log(v1 + "  " + lines[v1]);
    }
}
//-----------------------------

//js4________________________

//----------------

function tts_3_speak_a_line(objtxt_to_speak, wh) {
    if (sw_cancel) {
        TTS_LOOP_swLoop = false;
        sw_cancel = false;
        return;
    }
    //speech_rate  = last_rate;

    tts_3_set_speech_Parms(objtxt_to_speak);
    
	
    synth.speak(objtxt_to_speak);

} // end of tts_3_speak_a_line()
//-------------------------------------------


//---------------------
function tts_3_speech_end_fun() {

    x1_line++;

    if ((x1_line) >= textLines.length) {
        //console.log("tts_3_speech_end_fun()1");
        tts_3_end_speech(); // defined in the caller   **   Feb 11, 2023	
        return;
    }
    var objtxt_to_speak;
    //rigout += textLines[x1_line] + "<br>";



    if ((x1_line + 1) >= textLines.length) {
        //console.log("tts_3_speech_end_fun()2");
        tts_3_end_speech(); // defined in the caller   **   Feb 11, 2023	
        return;
    }
  	
    objtxt_to_speak = utteranceList[x1_line + 1];
    //speech = objtxt_to_speak; //2  

   
    objtxt_to_speak.onend = tts_3_speech_end_fun;

    //objtxt_to_speak.onend = (event) =>  {tts_3_speech_end_fun(event) } ;
 
    tts_3_speak_a_line(objtxt_to_speak, 2);

} // end of tts_3_speech_end_fun

//----------------------------------------------------------


//-------------------------------------------
var pLastBold_ix1 = -1; // phrase
var pLastBold_ix2 = -1;
var wLastBold_ix1 = -1; // word
var wLastBold_ix2 = -1;
//---------------------

function tts_3_remove_last_bold(id_pref, isWord) {

    var lastBold_ix1, lastBold_ix2;
    if (isWord) {
        lastBold_ix1 = wLastBold_ix1;
        lastBold_ix2 = wLastBold_ix2;
    } else {
        lastBold_ix1 = pLastBold_ix1;
        lastBold_ix2 = pLastBold_ix2;
    }
    if (lastBold_ix2 < 0) return;

    for (var v = lastBold_ix1; v <= lastBold_ix2; v++) {
        var ele1 = document.getElementById(id_pref + v);
        if (ele1 == false) continue;
        var ele1_tr = ele1.parentElement.parentElement;
        ele1.classList.remove("boldLine");
        ele1.style.backgroundColor = null;
        ele1.parentElement.style.border = null; // "1px solid red"; 
        ele1_tr.style.backgroundColor = "lightgrey"; // "yellow";	//feb	  
    }
    lastBold_ix2 = -1;
    if (isWord) {
        wLastBold_ix1 = lastBold_ix1;
        wLastBold_ix2 = lastBold_ix2;
    } else {
        pLastBold_ix1 = lastBold_ix1;
        pLastBold_ix2 = lastBold_ix2;
    }
} // end of tts_remove_last_bold()

//------------------------------

function tts_3_showHide_if_book_opened_from_to(id_pref, id_pref_idb, z3a, z3b) {
    var isWord = (id_pref.substr(0, 1) == "w");
    tts_3_word_removeLastBold(isWord);

    //console.log("2tts showHide " + z3a + " " + z3b );

    var ele_to_test = document.getElementById(id_pref_idb + z3a + "_m");


    if (ele_to_test.children[0].style.display == "block") { // openbook ==> show 
        for (var v = z3a; v <= z3b; v++) {
            var ele1 = document.getElementById(id_pref + v);
            var ele1_tr = ele1.parentElement.parentElement;
            //ele1.style.visibility = "visible"; 
            ele1.style.display = "block";
            ele1.classList.add("boldLine");
            ele1.style.backgroundColor = "yellow";
            ele1.parentElement.style.border = null;
            //feb if (sw_is_no_videoaudio == false) ele1_tr.style.backgroundColor = "yellow";		
            if (ele1_tr) ele1_tr.style.backgroundColor = "yellow"; //feb 	
        }
    }
    if (isWord) {
        wLastBold_ix1 = z3a;
        wLastBold_ix2 = z3b;
    } else {
        pLastBold_ix1 = z3a;
        pLastBold_ix2 = z3b;
    }

} // end of tts_3_showHide_if_book_opened_from_to()
//----------------------------------
function tts_3_showHide_if_book_opened(id_pref, id_pref_idb, z3) {
    var isWord = (id_pref.substr(0, 1) == "w");
    tts_3_word_removeLastBold(isWord);

    //console.log("1tts showHide " + z3 );

    var ele1 = document.getElementById(id_pref + z3);
    var ele_to_test = document.getElementById(id_pref_idb + z3);

    var ele1_tr = ele1.parentElement.parentElement;



    if (ele1 == null) {
        return;
    }
    if (last_blue_cell) {
        last_blue_cell.style.border = null;
    }
    if (ele_to_test.children[0].style.display == "block") { // openbook ==> show 
        //ele1.style.visibility = "visible"; 
        ele1.style.display = "block";
        ele1.classList.add("boldLine");
        ele1.style.backgroundColor = "yellow";
        ele1.parentElement.style.border = null;
        //feb if (sw_is_no_videoaudio == false) ele1_tr.style.backgroundColor = "yellow";			
        ele1_tr.style.backgroundColor = "yellow"; //feb 	
    } else { // closebook  ==> hide 
        //ele1.style.visibility = "hidden"; 	
        le1.style.display = "none";
        ele1.classList.remove("boldLine");
        ele1.style.backgroundColor = null;
        ele1.parentElement.style.border = "1px solid blue"; //red
        last_blue_cell = ele1.parentElement;
        //feb if (sw_is_no_videoaudio == false) ele1_tr.style.backgroundColor = "yellow";		
        //ele1_tr.style.backgroundColor = "yellow";	//feb	  
    }
    if (isWord) {
        wLastBold_ix1 = z3;
        wLastBold_ix2 = z3;
    } else {
        pLastBold_ix1 = z3;
        pLastBold_ix2 = z3;
    }

} // end of tts_showHide_ORIG_if_book_opened() 

//--------------------------------------------

function tts_3_end_speech_calculation() {

    // called by tts_3_end_speech() in cbc_player_script   and cbc_player_word_script

    var endTime = new Date();
    var timeDiff = endTime - startTime; //actual elapsed time in ms 

    if (txt_length < 1) {
        return;
    }


    var normal_time = timeDiff * speech_rate;

    //-----------
    tot_norm_time += normal_time;
    tot_txt_len += txt_length;
    tot_norm_mill_char = tot_norm_time / tot_txt_len;
    tot_norm_str_leng_limit = ELAPSED_TIME_SPEECH_LIMIT / tot_norm_mill_char;
    TXT_SPEECH_LENGTH_LIMIT = parseInt(tot_norm_str_leng_limit * speech_rate);

    tts_3_loopManager();

} // end of tts_3_end_speech_calculation() 
//-----------------------------------------

function tts_3_end_speech() {

    if (ele_last_play) {
        if (TTS_LOOP_swLoop == false) {
            ele_last_play.style.backgroundColor = null;
        }
    }
    tts_3_end_speech_calculation();
} // end of tts_3_end_speech()

//-------------------------------------------

function tts_3_loopManager() {

    if (sw_cancel) {
        TTS_LOOP_swLoop = false;
        sw_cancel = false;
    }
    if (TTS_LOOP_swLoop == false) return;

    lastNumVoice++;
    if (lastNumVoice >= totNumMyLangVoices) lastNumVoice = 0; // to change voice on each cycle

    var id_pref = "idc_";

    // wait 1 second and then start again  
    setTimeout(function() {
            if (TTS_LOOP_begix == TTS_LOOP_endix) {
                onclick_tts_text_to_speech_ix(id_pref, TTS_LOOP_begix, TTS_LOOP_swLoop, TTS_LOOP_elem);
            } else {
                onclick_tts_text_to_speech_from_to(id_pref, TTS_LOOP_begix, TTS_LOOP_endix, TTS_LOOP_swLoop, "1 loop_manager");
            }
        },
        1000);
} // end of tts_3_loopManager()


//--------------------------
function tts_3_boldCell(tr1, this1, ixVoice, wh) {
    if (lastBoldCell) {
        lastBoldCell.style.backgroundColor = null;
    }
    var selected_numVoices2 = 1;

    var td1 = this1.parentElement;
    var ixTab_TD = td1.cellIndex;

    var ixDiff = ixTab_TD - ixVoice;
    var ixTD_0 = 0;

    var num_tr_cells = tr1.cells.length;

    for (var n = 0; n < selected_numVoices2; n++) {
        ixTD_0 = n + ixDiff;
        if (n == ixVoice) {
            lastBoldCell = tr1.cells[ixTD_0];
            lastBoldCell.style.backgroundColor = "green";
        } else {
            tr1.cells[ixTD_0].style.backgroundColor = null;
        }
    }

} // end of tts_3_boldCell()

//--------

//---------------------------

function tts_3_breakTextToPause(txt3, pre_idtr1) {
    var g, ww2, txt4 = "";
    if (pre_idtr1 == "") {
        var ww1 = (txt3 + " ").replaceAll("–", " ").replaceAll("-", " ").
        replaceAll(", ", " ").replaceAll(" .", " ").replaceAll(". ", " ").replaceAll("...", " ").
        replaceAll("? ", " ").replaceAll("! ", " ").split(" ");

        for (g = 0; g < ww1.length; g++) {
            ww2 = ww1[g].trim();
            if (ww2 != "") txt4 += ww2 + ". ";
        }
    } else {
        var txt5 = (txt3 + " ").replaceAll("–", " ").replaceAll("-", " ").
        replaceAll(", ", " ").replaceAll(" .", " ").replaceAll(". ", " ").replaceAll("...", " ").
        replaceAll("? ", " ").replaceAll("! ", " ").trim();

        for (g = 0; g < txt5.length; g++) {
            ww2 = txt5.charAt(g);
            if (ww2 != "") txt4 += ww2 + ", ";
        }
		//console.log("tts_3_breakTextToPause() " +  txt3 + "\n" + txt4.replaceAll(",", "\n\t"));
    }
    return txt4;

} // end of breakToPause()	



//--------------------------------
function tts_3_onclick_tts_word_playSynthVoice_row2(this1, ixWord, swLoop, isWord, is_m1, swNewVoice) {
    var eleTR = this1.parentElement.parentElement;
    var id_tr = "";
    if (eleTR == "TR") {
        id_tr = eleTR.id;
    }

    if (swNewVoice) {
        lastNumVoice++;
        if (lastNumVoice >= totNumMyLangVoices) lastNumVoice = 0; // to change voice on each cycle
    } else {
        lastNumVoice = 0;
    }


    call_boldCell_ix(this1, lastWordNumVoice, "onclick_tts_word_OneClipRow_play_Loop3");

    onclick_tts_text_to_speech_ix("widc_", ixWord, false, this1);

} // end of onclick_tts_word_OneClipRow_play_Loop3()	



//---------------------------
function tts_3_removeBold_and_Font(txt0) {
    // I'm sorry<font color="#E5E5E5"> Val I'm frightfully tired but</font>
    //I&apos;m sorry&lt;font color=&quot;#E5E5E5&quot;&gt; Val I&apos;m frightfully tired but&lt;/font&gt;<br>
    let txt1 = txt0.trim().toLowerCase();
    txt1 = txt1.replaceAll("&lt;", "<").replaceAll("&gt;", ">").replaceAll("&apos;", "'").replaceAll("&quot;", '"');

    let j1 = -1;
    for (let x1 = 0; x1 < txt1.length; x1++) {
        j1 = txt1.indexOf("<font ");
        if (j1 < 0) {
            break;
        }
        if (txt1.indexOf("</font>", j1) < 0) {
            return txt1;
        }
        let j2 = txt1.indexOf(">", j1);
        if (j2 < 0) {
            break;
        }
        txt1 = txt1.substring(0, j1) + txt1.substring(j2 + 1);
        txt1 = txt1.replace("</font>", "");
    }
    txt1 = txt1.replace("< ", "<").replace(" >", ">").
    replaceAll("<em>", "").replaceAll("</em>", "").
    replaceAll("<strong>", "").replaceAll("</strong>", "").
    replaceAll("<b>", "").replaceAll("</b>", "").replaceAll("<i>", "").replaceAll("</i>", "").
    replaceAll("<B>", "").replaceAll("</B>", "").replaceAll("<I>", "").replaceAll("</I>", "");
    return txt1;

} // end of removeBold_and_Font()

//--------------------

function tts_3_play_or_cancel(this1) {
    if (synth.speaking) {
        if (ele_last_play) ele_last_play.style.backgroundColor = null;

        onclick_tts_speech_cancel();
        tts_3_end_speech();
        if (this1 == ele_last_play) { // click on the same line which is running ==> it means ==> I just want to stop it   
            return -1;
        }
        // click not on the sameline running ==> I wanted to stop the last line e start a new one 

    }

    this1.style.backgroundColor = "red";
    ele_last_play = this1;
    return 0;
}

//-------------------------------------

//-----------------------------------------------------------------
function tts_3_FAKE_onloaded_fun() {
    console.log("\nXXXXXXXXXXXXXXXXXXXXXXXXXX\nX tts_3_FAKE_onloaded_fun() \nXXXXXXXXXXXXXXXXXXXXXXXXXX\n");


    tts_3_fun_player_beginning();



} // end of tts_3_FAKE_onloaded_fun() 

//----------------------------------------------

//---------------------------------------------

function tts_3_fun_player_beginning() {

    console.log("\nXXXXXXXXXXXXXXXXXXXXXXXXXX\nX tts_3_fun_player_beginning() \nXXXXXXXXXXXXXXXXXXXXXXXXXX\n");


    ele_clip_subtext = document.getElementById("id_tabSub");

    MAX_ixClip = line_list_o_number_of_elements - 1;
    MIN_ixClip = 1;


    ele_dragSubT = document.getElementById("id_dragSub");
    ele_dragSubT_anchor = document.getElementById("id_dragSub_anchor");



    wScreen = screen.availWidth;
    hScreen = screen.availHeight;

    subtitles_beg_delta_time = 0;
    //src1 = document.getElementById("myVideo").src;

    lastClipTimeBegin = 0;
    lastClipTimeEnd = 0;

    MAX999 = 999999;


    sw_sub_orig = sw_inp_sub_orig_builder;
    sw_sub_tran = sw_inp_sub_tran_builder;
    sw_sub_onfile = (sw_sub_orig || sw_sub_tran);

    sw_no_subtitle = ((sw_sub_onfile == false)); // no subtitles ( neither inside the video, neither in any file apart

    if (sw_no_subtitle) {
        eleTabSub.style.display = "none";
    }
    //-------------------------------------------------------       
    // let lev2 
    path1 = window.location.pathname;
    f1 = path1.lastIndexOf("/");
    f2 = path1.lastIndexOf("\\");
    f3 = -1;
    barra = "/";
    if (f1 > f2) {
        f3 = f1;
        barra = "/";
    } else {
        f3 = f2;
        barra = "\\";
    }


    lastClipTimeBegin = 0;
    lastClipTimeEnd = 0;

    tts_5_get_tran_subtitle_text(); // must stay before 'get_orig_subtitle_text()'	
    tts_5_get_orig_subtitle_text();

    //console.log(number_of_subtitle_endsentence + "  number of subtitle lines ending a sentence (dialog end with end of sentence)");
    //console.log(number_of_subtitle_time_overlap + " number of subtitle lines with time overlap (dialog ends when there is no overlap)");


    line_list_o_number_of_elements = line_list_o_from1.length;
    line_list_t_number_of_elements = line_list_t_from1.length;

    if ((sw_sub_orig == false)) {
        document.getElementById("id_td_suborig2").style.display = "none";
    }

    if (sw_sub_tran == false) {
        document.getElementById("id_td_subtra2").style.display = "none";
    }



    LIMIT_MIN_TIME_CLIP = 0.100; // if time too near ( difference <  LIMIT_MIN_TIME_CLIP) to toTimeClip than use next clip number 

    tts_5_fun_update_html_with_last_session_values();

    //fun_set_next_div_via_cliptype(); 


    //-------------------------------

    tts_5_fun_setMinMaxIxClip();


    if (sw_is_no_videoaudio == false) {
        tts_5_fun_replace_video_src();
    }

	/**
    console.log("\nxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" +
        "\nsw_no_subtitle   = " + sw_no_subtitle +
        "\nsw_sub_onfile    = " + sw_sub_onfile +
        "\nsw_sub_orig      = " + sw_sub_orig + "   num." + line_list_orig_text.length +
        "\nsw_sub_tran      = " + sw_sub_tran + "   num." + line_list_tran_text.length +
        "\nxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
	**/

    if (sw_sub_onfile == false) {
        document.getElementById("id_labshowclip").style.display = "none";
        document.getElementById("id_inpshowclip").style.display = "none";

        document.getElementById("id_playNext2_line_row").style.display = "none";
        document.getElementById("id_replay2_line_row").style.display = "none";
    }



    tts_5_former_onclick_tts_ClipSub_All(); //  ...ClipSub_All(document.getElementById("id_inpshowclipA") ); 
    /**
    //subtitle_row_length2();
    onclick_tts_scroll_right( document.getElementById("id_bRigthLeft") ) ;
    onclick_tts_scroll_right( document.getElementById("id_bRigthLeft") ) ;
    onclick_tts_scroll_right( document.getElementById("id_bRigthLeft") ) ;
    **/

} // end of player script beginning 

//------------------------------------------------------------------------
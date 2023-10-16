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

function tts_5_get_orig_subtitle_text() {

    let i, row, from1, to1, max_to1, rowcol;

    line_list_o_from00 = [];
    line_list_o_to00 = []; //
    line_list_o_maxto00 = [];
    line_list_o_from1 = []; //
    line_list_o_to1 = []; //
    line_list_o_maxto1 = []; //
    line_list_orig_text = [];
	line_list_orig_nFileR = []; 
    line_list_orig_tts = [];
    line_list_o_tran_ixmin = [];
    line_list_o_tran_ixmax = [];

    line_list_o_from00.push(-1);
    line_list_o_to00.push(-1);
    line_list_o_maxto00.push(-1);


    line_list_o_from1.push(-1);
    line_list_o_to1.push(-1);
    line_list_o_maxto1.push(-1);

    line_list_orig_text.push("");
	line_list_orig_nFileR.push(""); 
    line_list_orig_tts.push("");
    line_list_o_tran_ixmin.push(0);
    line_list_o_tran_ixmax.push(0);


    if (sw_sub_orig == false) {
        return;
    }

    max_to1 = 0;
    to1 = 0;
    let ixmin = 0;
    let ixmax = 0;
    let tran_len = line_list_t_from1.length;
    //-------------------------
    let pre_from = 0;
    let pre_to1 = 0;

    let lastix = inp_row_orig.length - 1;

    for (i = inp_row_orig.length - 1; i > (inp_row_orig.length - 10); i--) {
        if (inp_row_orig[i].trim() == "") {
            continue;
        }
        row = inp_row_orig[i].trim();
        lastix = i;
        break;
    }
    from1 = 0;
    to1 = -1;
    let x1 = 0;
    let x2 = 0;

    number_of_subtitle_endsentence = 0;
    number_of_subtitle_time_overlap = 0;

    var rowtext, rowTTS;
	var cols = [];
	var nFileRow;
	//var nFileRow, nFile, nRows;
	var row123;
	
    //---------------------
    for (i = 0; i <= lastix; i++) {
        row = inp_row_orig[i].trim();
        if (row == "") {
            continue;
        }
		//if (row.substring(0,1) == ";") {row = row.substring(1)}
        pre_from = from1;
        pre_to1 = to1;

		// wbf:      ;;1;59;; BC DEF    ;;nFile;n.row;; row 
        cols     = (row + ";;;;;;").split(";;");
		nFileRow = cols[1].replace(";","_"); 
		//nFileRow = (cols[1]+";;;").split(";");
		//nFile    = nFileRow[0]; 
		//nRows    = nFileRow[1];
		row123   = cols[2]	  ; 
		//console.log( "??ANTO  row=" + row + "\n\tcols=" , cols, "\n\tnFileRow=" , nFileRow , "\n\tnFile="+nFile + " nRows=" + nRows + "  row123=" + row123 + "<==");  	
		rowcol   = [i, (i + 1), row123.trim()];
		
        //rowcol = [i, (i + 1), row];

        from1 = parseFloat(rowcol[0]);

        if (from1 < pre_from) {
            //     original language subtitle line ignored because not in sequence of time:  pre=" + pre_from + " now=" + row 
            continue;
        }

        if (from1 == pre_to1) { // to avoid that in the same moment there be 2 subtitles lines actives when actualy one is the following of the other  (upd 2022_03_16)

            from1 += 0.0004;
        }
        to1 = parseFloat(rowcol[1]);

        if (from1 < pre_to1) {
            number_of_subtitle_time_overlap++; // there is a time overlap ( the speaker begin to speak before the previous one have finished)
        }

        max_to1 = Math.max(max_to1, to1);


        line_list_o_from00.push(from1);
        line_list_o_to00.push(to1);
        line_list_o_maxto00.push(max_to1);

        line_list_o_from1.push(from1);
        line_list_o_to1.push(to1);
        line_list_o_maxto1.push(max_to1);


        //let rowtext = rowcol[2].trim();

        rowtext = rowcol[2].trim();
        rowTTS = tts_8_REPLACE(rowtext);

        //[rowtext, rowTTS] = splitTTS(  rowcol[2] ); 


        let lastchar = rowtext.substring(rowtext.length - 1);
        if ((".?!").indexOf(lastchar) >= 0) {
            number_of_subtitle_endsentence++;
        }


        line_list_orig_text.push(rowtext);
        line_list_orig_tts.push(rowTTS.trim());
		line_list_orig_nFileR.push( nFileRow );  

        x1 = ixmin;

        for (x1 = x1; x1 <= tran_len; x1++) {
            if (from1 >= line_list_t_from1[x1]) {
                ixmin = x1;
                continue;
            }
            ixmax = ixmin;
            for (x2 = ixmin; x2 <= tran_len; x2++) {
                if (to1 >= line_list_t_to1[x2]) {
                    ixmax = x2;
                    continue;
                }
                break;
            }
            break;
        }
        line_list_o_tran_ixmin.push(ixmin);
        line_list_o_tran_ixmax.push(ixmax);
    }

} // end of get_orig_subtitle_text() 
//---------------------------------------


function tts_5_get_tran_subtitle_text() {

    let i, row, from1, to1, max_to1, rowcol;
    line_list_t_from00 = [];
    line_list_t_to00 = []; //
    line_list_t_maxto00 = [];
    line_list_t_from1 = []; //
    line_list_t_to1 = []; //
    line_list_t_maxto1 = []; //
    line_list_tran_text = [];

    line_list_t_from00.push(-1);
    line_list_t_to00.push(-1);
    line_list_t_maxto00.push(-1);

    line_list_t_from1.push(-1);
    line_list_t_to1.push(-1);
    line_list_t_maxto1.push(-1);
    line_list_tran_text.push("");

    if (sw_sub_tran == false) {
        return;
    }
    max_to1 = 0;

    let lastix = inp_row_tran.length - 1;


    for (i = inp_row_tran.length - 1; i > (inp_row_tran.length - 10); i--) {
        if (inp_row_tran[i].trim() == "") {
            continue;
        }
        row = inp_row_tran[i].trim();
        lastix = i;
        break;
    }
	var cols = [];
	//var nFileRow, nFile, nRows, 
	var row123;
    let pre_from, pre_to1;
    from1 = 0;
    to1 = -1;
    //-------------------------
    for (i = 0; i <= lastix; i++) {
        row = inp_row_tran[i].trim();
        if (row == "") {
            continue;
        }
		//if (row.substring(0,1) == ";") {row = row.substring(1)}
        pre_from = from1;
        pre_to1 = to1;
        //rowcol = [i, (i + 1), row];
		//------------------------
		// wbf:      ;;1;59;; BC DEF    ;;nFile;n.row;; row 
        cols     = (row + ";;;;;;").split(";;");
		/**
		nFileRow = (cols[1]+";;;").split(";");
		nFile    = nFileRow[0]; 
		nRows    = nFileRow[1];
		**/
		row123   = cols[2]	  ; 
		//console.log( "??ANTO  row=" + row + "\n\tcols=" , cols, "\n\tnFileRow=" , nFileRow , "\n\tnFile="+nFile + " nRows=" + nRows + "  row123=" + row123 + "<==");  	
		rowcol   = [i, (i + 1), row123.trim()];
		//------------	
		
        from1 = parseFloat(rowcol[0]);

        if (from1 < pre_from) {
            //   translated language subtitle line ignored because not in sequence of time:  pre=" + pre_from + " now=" + row );
            continue;
        }
        if (from1 == pre_to1) { // to avoid that in the same moment there be 2 subtitles lines actives when actualy one is the following of the other  (upd 2022_03_16)
            from1 += 0.0004;
        }

        to1 = parseFloat(rowcol[1]);
        max_to1 = Math.max(max_to1, to1);


        line_list_t_from00.push(from1);
        line_list_t_to00.push(to1);
        line_list_t_maxto00.push(max_to1);

        line_list_t_from1.push(from1);
        line_list_t_to1.push(to1);
        line_list_t_maxto1.push(max_to1);

        line_list_tran_text.push(rowcol[2]);
    }

} // end of get_tran_subtitle_text() 


//-----------------------------------------------------------
function tts_5_fun_update_html_with_last_session_values() {

    if ((sw_no_subtitle) || (sw_sub_onfile == false)) {
        LS_clip_checked_sw_type = radio_type1_SECONDS; // only clip in seconds 

    }
    if ((typeof LS_clip_checked_sw_type === "undefined") || (LS_clip_checked_sw_type == "")) {
        LS_clip_checked_sw_type = radio_type1_SECONDS; // only clip in seconds 

    }


    let p_list = LS_stor_playnext_replay.split(";;");


    ele_playNextVa_from_hhmmss_value = p_list[0];
    ele_replayVa_from_hhmmss_value = p_list[1];
    ele_replayVa_to_hhmmss_value = p_list[2];
    if (ele_playNextVa_from_hhmmss_value == 0) {
        ele_playNextVa_from_hhmmss_value = "00:00:00.000";
    }
    if (ele_replayVa_from_hhmmss_value == 0) {
        ele_replayVa_from_hhmmss_value = "00:00:00.000";
    }
    if (ele_replayVa_to_hhmmss_value == 0) {
        ele_replayVa_to_hhmmss_value = "00:00:00.000";
    }


    if (ele_replayVa_from_hhmmss_value < ele_playNextVa_from_hhmmss_value) {
        ele_playNextVa_from_hhmmss_value = ele_replayVa_from_hhmmss_value;
    }

    let secs4 = tts_5_fun_N_hhmmss_to_secs(ele_replayVa_to_hhmmss_value);


    let hhmmss4 = tts_5_fun_N_secs_to_hhmmssmmm(secs4 - 1.0);
    ele_replayVa_to_hhmmss_value = hhmmss4;

    if (sw_is_no_videoaudio == false) {
        if (vid) {
            vid.currentTime = secs4;
        }
    }

    let secs1d = ("0" + LS_clip_secs1d_value + "-false-true").split("-");

    let end_dialog_sentence = secs1d[1].trim();
    let end_dialog_overlap = secs1d[2].trim();

    //-----------
    end_dialog_sentence = "false";
    end_dialog_overlap = "false";
    sw_end_dialog_sentence = false;
    sw_end_dialog_overlap = false;

    if ((number_of_subtitle_endsentence == 0) && (number_of_subtitle_time_overlap == 0)) {
        //document.getElementById("irad_r1").style.display = "none"; 		
    } else {
        if (number_of_subtitle_time_overlap > 0) {
            end_dialog_overlap = "true";
            sw_end_dialog_overlap = true;
        }
        if (number_of_subtitle_endsentence > 0) {
            end_dialog_sentence = "true";
            sw_end_dialog_sentence = true;
        }
    }


    tts_5_fun_update_LS_sub_endbeg_delta();



} // end of fun_update_html_with_last_session_values()

//-------------------------------------------------------------------------------	

function tts_5_fun_N_hhmmss_to_secs(x) {
    let col00 = ("0:0:0:" + x.toString().replace(",", ".")).split(":");
    let col = col00.slice(-3);

    let hh1 = col[0] * 3600;
    let mm1 = col[1] * 60;
    let ss1 = col[2] * 1;

    let secs = Math.round((hh1 + mm1 + ss1) * 1000) / 1000;
    return secs;
}

//--------------------------------------------------

function tts_5_fun_N_secs_to_hhmmssmmm(from1) {
    // surely a film lasts less than 10 hour

    if ((isNaN(from1)) || (from1 == 0)) {
        return "00:00:00.000";
    }
    let secs = 3600 * 10 + 1 * from1;

    let hhmmss2 = new Date(secs * 1000).toISOString().substr(11, 12);
    let hhmmss = "0" + hhmmss2.substring(1);

    return hhmmss;
}

//------------------------------

function tts_5_fun_update_LS_sub_endbeg_delta() {

    if (isNaN(LS_sub_beg_delta)) {
        LS_sub_beg_delta = parseFloat("0" + LS_sub_beg_delta);
    }
    if (isNaN(LS_sub_end_delta)) {
        LS_sub_end_delta = parseFloat("0" + LS_sub_end_delta);
    }

    let beg_val = LS_sub_beg_delta; // can be positive or negative 
    let end_val = LS_sub_end_delta; // can be positive or negative 
  
    let beg_PM = "plus";
    let end_PM = "plus";
    if (beg_val < 0) {
        beg_PM = "minus";
    }
    if (end_val < 0) {
        end_PM = "minus";
    }
   
}

//--------------------------------------------

function tts_5_fun_setMinMaxIxClip() {

    MIN_ixClip = 0;
    MAX_ixClip = 0;

    if (line_list_o_from1.length > 3) {
        MAX_ixClip = line_list_o_to1.length - 1;
        return;
    }
    return;
}

//-------------------------------------------

function tts_5_former_onclick_tts_ClipSub_All(this1) {

    var this1_checked = true;

    var sw_all = true;
  
    if (sw_sub_onfile == false) {
        return;
    }
    if (sw_sub_orig == false) {
        return;
    }

    save_last_oneOnlyRow = "";
    save_last_oneOnly_idtr = "";

    ele_last_tran_line = null;

    if (this1_checked == false) {
        fun_checked_false_goBack(this1);
        console.log("\tonclick_tts_ClipSub_All() return ");
        return;
    }



    tts_5_fun_build_all_clip();

   

    if (sw_all) {
        clipFromRow = clipFromRow_min;
        clipToRow = line_list_orig_text.length - 1;
        sw_CLIP_play = true;
        Clip_startTime = 0;
        if (sw_is_no_videoaudio == false) {
            Clip_stopTime = vid.duration;
        }
    } else {
        clipFromRow = parseInt(ele_replayVa_from_row_value);
        clipToRow = parseInt(ele_replayVa_to_row_value);
        sw_CLIP_play = true;
        Clip_startTime = parseFloat(ele_replay_from_secs_innerHTML);
        Clip_stopTime = parseFloat(ele_replay_to_secs_innerHTML);
    }

    //  xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx  now html elements for clip section are ready xxxxxxxxxxxxxxxxxxxxxxxxxxxx

    let eleF = document.getElementById("b1_" + clipFromRow);
    let eleT = document.getElementById("b2_" + clipToRow);

    //onclick_tts_arrowFromIx(eleF, clipFromRow, "2 tts_5_former_onclick_tts_ClipSub_All()" );
    //onclick_tts_arrowToIx(eleT, clipToRow);



    ele_clip_subtext.style.display = "block";


    //-------------------
    //set new dimension to be the almost the body dimension 

 
    let new_eleTabSub_clientWidth = eleTabSub.clientWidth;
    let new_eleTabSub_clientHeight = eleTabSub.clientHeight;
    //--- translate to style width/height
    eleTabSub.style.width = (new_eleTabSub_clientWidth - eleTabSub_diff_clientW) + "px"; // set  new dimension			
    eleTabSub.style.height = (new_eleTabSub_clientHeight - eleTabSub_diff_clientH) + "px"; // set  new dimension
    //----------------

    var elediv20 = document.getElementById("id_div20");

    clip_reset_BG_color = tts_5_get_backgroundColor(elediv20);
    eleTabSub.style.backgroundColor = clip_reset_BG_color;
    ele_clip_subtext.style.backgroundColor = clip_reset_BG_color;

} // end of former_onclick_tts_ClipSub_All()

//---------------------------------------------


//-----------------

function tts_5_fun_build_all_clip() {
   
    if (sw_sub_onfile == false) {
        return;
    }
    if (sw_sub_orig == false) {
        return;
    }

    save_last_oneOnlyRow = "";
    save_last_oneOnly_idtr = "";

    ele_last_tran_line = null;
   

    let clipSub_showTxt, txt1;
   

    clipFromRow = 0;
    clipToRow = line_list_orig_text.length - 1;


    sw_CLIP_play = true;
    Clip_startTime = 0;


    //--------------------------	
    var z3Beg = 0;
    for (let z3 = clipFromRow; z3 <= clipToRow; z3++) {
        txt1 = line_list_orig_text[z3].trim();
        if (txt1 == "") {
            continue;
        }
        if (txt1 == "_.") {
            continue;
        }
        z3Beg = z3;
        break;
    }
    if (z3Beg > clipFromRow) {
        clipFromRow = z3Beg;
        clipFromRow_min = clipFromRow;
    }

    begix = clipFromRow;
    endix = clipToRow;
    var text_tts;
    clipSub_showTxt = "\n";

	
	var word3="", ixUnW3="", totRow3="", wLemma3="", wTran3="";
	
	if (word_to_underline != "") {
		[word3, ixUnW3, totRow3, wLemma3, wTran3] = word_to_underline.split(",")
	}	
	if ((wLemma3 == "-") || (wLemma3 == "")) { wLemma3 = word3; }     
	
	var wordToBold = word3; 
	var wordLemma  = wLemma3;
	var wordTran   = wTran3; 
	var head1 = '<span style="color:blue;">' + wordLemma + '</span>' + 
		    '<br><span style="font-size:0.8em;">' + wordTran + '</span>';  
	document.getElementById("id_headWord").innerHTML = head1; 
	if ((word3=="") || (word3 == undefined)) {head1="";} 
	document.getElementById("id_headWord").style.textAlign = "center";
	var nFileR ; var nfile_zero
	
    for (let z3 = clipFromRow; z3 <= clipToRow; z3++) {

        txt1 = line_list_orig_text[z3];
        text_tts = line_list_orig_tts[z3].trim();

        let trantxt1 = "";
		let txt1p=""; 

        for (let g = line_list_o_tran_ixmin[z3]; g <= line_list_o_tran_ixmax[z3]; g++) {
            let txt2 = line_list_tran_text[g];
            if (txt2.indexOf(sayNODIALOG) >= 0) {
                txt2 = "...";
            }
            trantxt1 += "<br>" + txt2;
        }
        if (trantxt1.substr(0, 4) == "<br>") {
            trantxt1 = trantxt1.substring(4);
        }
		txt1p = evidenzia( wordToBold , txt1);      // function defined  in "wordsByFrequence.js" file
		
		nFileR = line_list_orig_nFileR[z3] 
		if (nFileR.substr(0,1) == "0") { nfile_zero = "0";} else {nfile_zero="1";}
		
		
        let rowclip = string_tr_xx.replaceAll("§1§", z3).
			replaceAll("§4txt§", txt1).replaceAll("§5txt§", trantxt1).
			replaceAll("§4ptxt§", txt1p).
			replaceAll("§ttstxt§", text_tts).
			replaceAll("§6§", nFileR ).
			replaceAll("§nfile§",nfile_zero)	;		
        
		clipSub_showTxt += rowclip + "\n";
		
			
    } // end of for z3
  

    eleTabSub_tbody.innerHTML = clipSub_showTxt;



    sw_tts = true;



    //  xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx  now html elements for clip section are ready xxxxxxxxxxxxxxxxxxxxxxxxxxxx

    let eleF = document.getElementById("b1_" + clipFromRow);
    let eleT = document.getElementById("b2_" + clipToRow);


    onclick_tts_arrowFromIx(eleF, clipFromRow, "1 tts_5_fun_build_all_clip()"  );
    onclick_tts_arrowToIx(eleT, clipToRow);



    ele_clip_subtext.style.display = "block";

    //-------------------
    //set new dimension to be the almost the body dimension 

    let new_eleTabSub_clientWidth = eleTabSub.clientWidth;
    let new_eleTabSub_clientHeight = eleTabSub.clientHeight;
    //--- translate to style width/height
    eleTabSub.style.width = (new_eleTabSub_clientWidth - eleTabSub_diff_clientW) + "px"; // set  new dimension			
    eleTabSub.style.height = (new_eleTabSub_clientHeight - eleTabSub_diff_clientH) + "px"; // set  new dimension
    //----------------

    var elediv20 = document.getElementById("id_div20");

    clip_reset_BG_color = tts_5_get_backgroundColor(elediv20);
    eleTabSub.style.backgroundColor = clip_reset_BG_color;
    ele_clip_subtext.style.backgroundColor = clip_reset_BG_color;

} // end of fun_build_all_clip()  

//----------------------------------------------------

//------------------------------------------------
function tts_5_highlightRow(ele1) {
    tts_5_removeLastBold();

    ele1.classList.add("boldLine");
    ele1.style.backgroundColor = "yellow";
    ele1.parentElement.style.border = "1px solid black";

    last_BoldRow = ele1;
}
//-------------------------
function tts_5_removeLastBold() {
    if (last_BoldRow) {
        //console.log("removeLastBold() " + last_BoldRow.id);
        var epar1 = last_BoldRow.parentElement;
        if (epar1) {
            //console.log("\tlast_BoldRow.parentElement.id=" + epar1.id);
            var epar2 = epar1.parentElement;
            if (epar2) {
                //console.log("\tlast_BoldRow.parentElement.parentElement.id=" + epar2.id);
            } else {
                //console.log("\tlast_BoldRow.parentElement.parentElement missing");
            }
        } else {
            //console.log("\tlast_BoldRow.parentElement missing");
        }


        last_BoldRow.classList.remove("boldLine");
        last_BoldRow.style.backgroundColor = null;
        last_BoldRow.parentElement.style.border = null;
        var last_ele1_tr = last_BoldRow.parentElement.parentElement;
        last_ele1_tr.style.backgroundColor = "lightgrey";
    }
    //if (sw_tts) tts_3_remove_last_bold("idc_", false);
	if (sw_tts) tts_3_remove_last_bold("idp_", false);
}

//---------------------------------------

function tts_5_fun_invisible_prev_fromto(interX) {
    // eliminate bold of the  previous group of lines, unless this is a line in them  
    [begix, endix] = fromIxToIxLimit; // previously set 
    if ((interX >= begix) && (interX <= endix)) {
        return;
    }
    var id_pre_tr_beg_space = "idtr_" + begix + "_m2";
    var id_pre_tr_head = "idtr_" + begix + "_m1";
    var id_post_tr_end_space = "idtr_" + (endix + 1) + "_m2";


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

} // end of fun_invisible_prev_fromto()

//------------------------------------------

function tts_5_fun_copy_openClose_to_tr_m1(z3) {

    var i_eleSubO = document.getElementById("idb_" + z3); // from button id="idb_§1§"    onclick_tts_show_row()
    var i_eleSubT = document.getElementById("idbT_" + z3); // from button id="idbT_§1§"   onclick_tts_show_row() 
    var o_eleSubO = document.getElementById("idb_" + z3 + "_m"); // to   button id="idb_§1§_m"  onclick_tts_OneClipRow_showHide_sub()
    var o_eleSubT = document.getElementById("idbT_" + z3 + "_m"); // to   button id="idbT_§1§_m" onclick_tts_OneClipRow_showHide_tran()		
	//console.log("tts_5_fun_copy... z3=", z3, " o_eleSubO.id=",  o_eleSubO.id , "  numChold=" , o_eleSubO.children.length) 
    try {
        o_eleSubO.children[0].style.display = i_eleSubO.children[0].style.display; // ${openbook_symb}
        o_eleSubO.children[1].style.display = i_eleSubO.children[1].style.display; // ${closedbook_symb}
        o_eleSubT.children[0].style.display = i_eleSubT.children[0].style.display; // ${show_translation_symb}
        o_eleSubT.children[1].style.display = i_eleSubT.children[1].style.display; // ${hide_translation_symb}
    } catch (e1) {
        console.log("error in 'fun_copy_openClose_to_tr_m1(z3=" + z3 + ")'");
        console.log(e1);
    }
} // end of fun_copy_openClose_to_tr_m1() 

//-------------------------------------------

//-----------------------------------------------
function tts_5_fun_copyHeaderSelected() {

    let id1;
    let inBeg, inEnd;

    id1 = "idb_" + begix + "_m";
    var thisX = document.getElementById(id1);
    if (thisX == false) {
        return;
    }

    inBeg = begix;
    inEnd = endix;
    if (begix > endix) {
        inBeg = endix;
        inEnd = begix;
    }

    var style0, style1;

    tts_5_fun_oneRowZZ();

    for (var g = inBeg; g <= inEnd; g++) {
        id1 = "idb_" + g;
        thisX = document.getElementById(id1);
        tts_5_fun_oneRow11H();
    }

    //--------------
    function tts_5_fun_oneRowZZ() {
        if (thisX == false) {
            return;
        }

        if (thisX.children[0].style.display == "none") { // no openbook   
            style0 = "none"; //  hide opened book image  
            style1 = "block"; //  show closed book image 
        } else {
            style0 = "block"; // show opened book image  
            style1 = "none"; // hide closed book image 	
        }
    }
    //--------------
    function tts_5_fun_oneRow11H() {
        if (thisX == false) {
            return;
        }
        thisX.children[0].style.display = style0; // show/hide  opened book image  
        thisX.children[1].style.display = style1; // show/hide closed book image 
        let subid = thisX.id.replace("idb", "idc");

        if (subid.substring(subid.length - 2) == "_m") {
            return;
        }
        let ele1 = document.getElementById(subid);
        if (style0 == "block") {
            tts_5_fun_makeTextVisible(ele1);
        } else {
            tts_5_fun_makeTextInvisible(ele1);
        }
    }
} // end of fun_copyHeaderSelected()

//-----------------------------
//----------------------------
function tts_5_fun_makeTextInvisible(element) {
    if (element) element.style.display = "none";
}
//----------------------------
function tts_5_fun_makeTextVisible(element) {
    if (element) element.style.display = "block";
}

//----------------------------------------------

//------------------------------------------
function tts_5_get_backgroundColor(ele0) {
    // since the backgroundColor is not inherited the 'getComputedStyle()' cannot get it from the parent  
    var ele1 = ele0;
    var eleP = ele1;
    for (var i = 0; i < 99; i++) {
        ele1 = eleP;
        if (ele1 == null) {
            return "";
        }
        var bgColor = window.getComputedStyle(ele1).getPropertyValue("background-color");
        var bgc1 = bgColor.split("(");
        var bgc2 = bgc1[1].split(")");
        var bgx = (bgc2[0].replaceAll("  ", "").replaceAll(" ", "").replaceAll(",", " ").trim()).substring(0, 7);
        if (bgx == "0 0 0 0") {
            eleP = ele1.parentElement;
        } else {
            //console.log(" get_backgroundColor(ele1=" + ele1.id + ")  ==> bgColor=" + bgColor); 
            return bgColor;
        }
    }
    console.log(" get_backgroundColor(ele1)  ==> bgColor=" + "  empty2");
    return "";
}

//-------------------------
function tts_5_show_hideORIG(z3) {
    let ele_orig_toTestShow = document.getElementById("idb_" + z3); // onclick ...  children opened/closed orig.image  (book) 		
    //let ele_orig_text = document.getElementById("idc_" + z3); // element of original text to show/hide	  			
	let ele_orig_text = document.getElementById("idp_" + z3); // element of original text to show/hide	  	
    // show subtitle if icon opened book is visible otherwise hide it ( icon closed book is visible) 
    tts_5_fun_oneClipRow_showHide_ORIG_if_book_opened(ele_orig_text, ele_orig_toTestShow, z3);
} // end of  show_hideORIG
//-------------------------
function tts_5_show_hideTRAN(z3) {

    let ele_tran_toTestShow = document.getElementById("idbT_" + z3); // onclick ...  children opened/closed tran.image  (T/t) 
    let ele_tran_text = document.getElementById("idt_" + z3); // element of tran     text to show/hide	      

    // show subtitle if icon T is visible otherwise hide it ( icon t? is visible  )	
    tts_5_fun_oneClipRow_showHide_TRAN_if_book_opened(ele_tran_text, ele_tran_toTestShow);

} // end of  show_hideTRAN
//-----------------------------------------------------

//-------------------------------------------
function tts_5_fun_oneClipRow_showHide_ORIG_if_book_opened(ele1, ele_to_test, z3) {

    var ele1_tr = ele1.parentElement.parentElement;

    tts_5_removeLastBold();

    if (ele1 == null) {
        return;
    }

    last_BoldRow = ele1;

    if (ele_to_test.children[0].style.display == "block") { // openbook ==> show 		
        ele1.style.display = "block";
        ele1.classList.add("boldLine");
        ele1.style.backgroundColor = "yellow";
        ele1.parentElement.style.border = null;
        ele1_tr.style.backgroundColor = "yellow"; //feb 		
    } else { // closebook  ==> hide 
        ele1.style.display = "none";
        ele1.classList.remove("boldLine");
        ele1.style.backgroundColor = null;
        ele1.parentElement.style.border = "1px solid red";
    }

    //last_BoldRow = ele1; 

} // end of fun_oneClipRow_showHide_ORIG_if_book_opened() 

//-------------------------------------------
function tts_5_fun_oneClipRow_showHide_TRAN_if_book_opened(ele1, ele_to_test) {

    if (ele1 == null) {
        return;
    }

    if (ele_to_test.children[0].style.display == "block") { // openbook ==> show 
        ele1.style.display = "block";
    } else { // closebook  ==> hide 
        ele1.style.display = "none";
    }


} // end of fun_oneClipRow_showHide_TRAN_if_book_opened() 
//-----------------------------------------


//---------------------------------------

function tts_5_fun_scroll_tr_toTop( this1, swDeb ){

	var ele_tr_target = this1; // .parentElement.parentElement ; 
	var numid= parseInt(ele_tr_target.id.substring(5).split("_")[0] );  // id="idtr_xx"   id="idtr_xx_m1"	
	
	if (swDeb) console.log("fun_scroll_tr_toTop() 1 numid=" + numid); 
	
	var ele_tr_nearest, diff_off=0;
	if (numid > 1) {
		ele_tr_nearest = document.getElementById(  "idtr_" +(numid-1)); 	
		if (ele_tr_nearest) {
			diff_off = ele_tr_target.offsetTop - ele_tr_nearest.offsetTop; 	
		}
	} else {
		ele_tr_nearest = document.getElementById(  "idtr_" +(numid+1)); 			
		if (ele_tr_nearest) {
			diff_off = 0 - (ele_tr_target.offsetTop - ele_tr_nearest.offsetTop); 	
		}
	}	
	var ele_container = document.getElementById("id_section_row");
	if (swDeb) { 
		var compHeight = window.getComputedStyle(ele_container).getPropertyValue("height");	
	
		console.log("fun_scroll_tr_toTop() 2  ele_tr_target.offsetTop - diff_off=" +  ele_tr_target.offsetTop + " - " + diff_off );
	    console.log("   ele_container  (id_tabSub).id = " + ele_container.id +
			" offsetHeight=" + ele_container.offsetHeight + " offsetTop=" + ele_container.offsetTop + 
			" style.height=" + ele_container.style.height + " computed height=" + compHeight);  
	} 
	if (numid < 2) {
		ele_container.scrollTop = 0; 
		return; 
	}
	try{
		ele_container.scrollTop = ele_tr_target.offsetTop - diff_off;
	} catch(e1) {
		console.log("fun_scroll_tr_toTop(this1)" + " this1.id=" + this1.id ); 
		console.log("  \t ele_tr_target.id=" + ele_tr_target.id); 
		ele_container.scrollTop = ele_tr_target.offsetTop - diff_off;
	}
} // end of fun_scroll_tr_toTop() 
//-------------------------------------------
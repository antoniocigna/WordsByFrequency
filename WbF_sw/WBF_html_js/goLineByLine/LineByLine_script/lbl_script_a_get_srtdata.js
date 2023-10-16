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
// the functions in this file are copied from the "builder" part of "ClipByClip" and "RaS" function
//----------------------------------------------------------------------------------------------------

function get_subtitle_strdata(inpsub) {
    //---------------------------------------
    // get subtitles in srt or vtt format 
    // and return a string with a line for each subtitle group     
    //---------------------------------------
    /* 
		sample of a srt file
			14
			00:01:08,000 --> 00:01:10,000      ixtime[13] = 52
			one line of text
			other lines of text
			 
			15
			00:01:10,000 --> 00:01:15,000      ixtime[14] = 57
			lines
			of texts   
		---------------------------------------------
		sample of a vtt file 
			WEBVTT                             (this is the first line which identify a webvtt subtitle file  		
			STYLE
			::cue(.S1) {
			color: white;
			...
			}
			REGION
			id:R1
			...

			1
			00:00:01.000 --> 00:00:02.040 region:R1 align:center
			<c.S1>one line</c>

			2
			00:00:02.600 --> 00:00:03.640 region:R1 align:center
			<c.S1>another line</c>

    */
    //-------------------------------------------------------


    var subline = inpsub.trim().split("\n"); // <===  INPUT  

    //----------------------------
    var i, txt1;



    var list_time_from = [0];
    var list_time_to = [0];
    var list_text = [""];
    var idsrt = [0];
    //------------------------------
    subline.push("");

    // look at what follows the time line,  stop when there is a blank line ( but might be missing ) 

    //list_start=[];  
    var line = "";
    var preline = "";

    var list_ix_beg = [0];
    var list_ix_end = [0];

    list_time_from = [0];
    list_time_to = [0];
    list_text = [""];
    idsrt = [""];
    var num = 0;
    /***
    subline.push(""); 
    subline.push("99999999"); 
    subline.push("99:99:99,999 --> 99:99:99,999"); 
    **/

    var isTime;
    var time_err;
    var timehh_fromX;
    var timehh_toX;

    //---
    function close_previous_group() {
        // the previous line should be a number 
        num = list_ix_end.length - 2;
        if (list_ix_beg[num] >= 0) {
            if (isNaN(preline)) {
                list_ix_end[num] = i;
            } else {
                list_ix_end[num] = i - 1;
            }
        }
    } //end of  close_previous_group()

    //-----------------------------------
    for (i = 0; i < subline.length; i++) {
        preline = line;
        line = subline[i];
        [isTime, time_err, timehh_fromX, timehh_toX] = isTimeLine(line);
        if (isTime == false) {
            continue;
        }
        if (time_err) {
            // error in time line
            list_ix_beg.push(-1);
            list_ix_end.push(-1);
            list_time_from.push(0);
            list_time_to.push(0);
            list_text.push("");
            idsrt.push("");
            close_previous_group();

            continue;
        }

        var timehh_from = timehh_fromX[1];
        var timehh_to = timehh_toX[1];

        var time_secs_from = timehh_fromX[0];
        var time_secs_to = timehh_toX[0];

        list_ix_beg.push(i);
        list_ix_end.push(i);


        list_time_from.push(time_secs_from);
        list_time_to.push(time_secs_to);

        list_text.push("");

        idsrt.push(timehh_from + " " + timehh_to);
        close_previous_group();

    }

    list_ix_end[list_ix_end.length - 1] = subline.length;


    var txt00;
    for (var k = 1; k < list_ix_end.length; k++) {
        txt1 = "";
        var ixfrom = list_ix_beg[k];
        if (ixfrom < 0) {
            continue;
        }
        var ixto = list_ix_end[k];
        for (var z = ixfrom + 1; z < ixto; z++) {
            txt00 = subline[z].trim();

            //console.log("z=" + z + " " + subline[z] + "<==");

            if (txt00 != "") txt1 += "\n" + txt00 + " ";
        }
        list_text[k] = txt1.substring(1);
    }

    return [list_time_from, list_time_to, list_text, idsrt];


    // add_nodialog_clips2( list_time_from, list_time_to, list_text ,idsrt );	

} // end of get_subtitle_strdata()
//----------------------------------

function get_timehhmmss(str0) {
    /*
    	try to manager time in srt or vtt  even when non correctly written ( maybe it's out of automatic translation)

    	expected ==>    00:12:45,123                   ( hh:mm:ss,mmmm ) 
    					00:12:45.123 other staff vtt   ( hh:mm:ss.mmmm )
    					00:12:45                       ( hh:mm:ss ) 	
    	can manage	1: 2: 45,123      transformed to 00:02:45.123
    				12:45,123         transformed to 00:12:45.123
    				45,123            transformed to 00:00:45.123					
    */

    var str1 = (str0 + "").trim().replace(",", ".").replaceAll(": ", ":").replaceAll(": ", ":");

    var tt1 = str1.split(":");
    var len1 = tt1.length;
    if (len1 < 3) {
        str1 = "00:" + str1;
        if (len1 < 2) {
            str1 = "00:" + str1;
        }
        tt1 = str1.split(":");
    }
    var tHH = tt1[0].trim();
    var tMM = tt1[1].trim();
    var tSS = tt1[2].trim().split(" ")[0]; // ignore whatever follows ( that is the case of vtt subtitiles) 


    if (isNaN(tHH)) {
        return;
    }
    if (isNaN(tMM)) {
        return;
    }
    if (isNaN(tSS)) {
        return;
    }
    var nHH = parseInt(tHH);
    var nMM = parseInt(tMM);
    var nSS = parseFloat(tSS);


    if ((nHH >= 60) || (nHH < 0) || (nMM >= 60) || (nMM < 0) || (nSS >= 60) || (nSS < 0)) {
        return;
    }

    var seconds = nHH * 3600 + nMM * 60 + nSS;

    tHH = (100 + nHH).toString().substring(1);
    tMM = (100 + nMM).toString().substring(1);
    tSS = (100.0000001 + nSS).toString().substr(1, 6);

    return [seconds, tHH + ":" + tMM + ":" + tSS];

} // end of get_timehhmmss(); 

//----------------------------------------

function isTimeLine(str1) {

    var line = str1.trim().
    replace("- ->", "-->").
    replace(" -> ", " --> ").
    replace("-- >", "-->"); // replace used to avoid random error from automatic translation  
    if (line.indexOf("-->") < 0) {
        return [false, true, "", ""];
    }
    var part = line.split("-->");
    var timehh_fromX = get_timehhmmss(part[0]);
    var timehh_toX = get_timehhmmss(part[1]);

    if ((timehh_fromX === undefined) || (timehh_toX === undefined)) {
        console.log("error in " + line);
        return [true, true, part[0], part[1]];
    }

    return [true, false, timehh_fromX, timehh_toX];
}
//==============================================================================
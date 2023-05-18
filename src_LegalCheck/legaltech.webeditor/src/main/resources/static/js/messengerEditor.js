var myVar = setInterval(fire_ajax_logger, 1000);

//window.onload = fire_ajax_submitContract();

function removeAllChildNodes(parent) {
	if (parent == null)
		return;
	while (parent.firstChild) {
		parent.removeChild(parent.firstChild);
	}
}

function fire_ajax_submitContract() {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	//console.log(csrfToken);
	//console.log(sessionID);
	//console.log(csrfHeader);
	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/legalContract?",
		data: JSON.stringify(sessionID),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			var dat2 = data["contract"];
			if (dat2) {
				var para2 = document.createElement("div");
				$(para2).html(dat2);
				var ele = document.getElementById("contractEle");
				removeAllChildNodes(ele);
				ele.appendChild(para2);
			}
		},
		error: function(e) {
			var json = "<h4>Ajax Error Submit</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

function fire_ajax_getParas() {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	//console.log(csrfToken);
	//console.log(sessionID);
	//console.log(csrfHeader);
	var data2 = {};
	var vars = [];
	data2["sessionID"] = sessionID;
	var count = 1;
	var node = document.getElementById("var" + count + "_value");
	var nodeOn = document.getElementById("var" + count + "_on");
	while (node != null) {
		//console.log("" + node.id);
		if (nodeOn.value != 0) {
			//console.log("" + nodeOn.value);
			vars.push(node.name);
			vars.push(node.value);
		}
		count++;
		node = document.getElementById("var" + count + "_value");
		nodeOn = document.getElementById("var" + count + "_on");
	}
	data2["vars"] = vars;

	//delete old results
	var eleR = document.getElementById("result");
	removeAllChildNodes(eleR);

	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/getparas",
		data: JSON.stringify(data2),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			var dat2 = data["contract"];
			if (dat2) {
				var para2 = document.createElement("div");
				$(para2).html(dat2);
				var ele = document.getElementById("paras");
				removeAllChildNodes(ele);
				ele.appendChild(para2);
			}
		},
		error: function(e) {
			var json = "<h4>Ajax Error Submit</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

function changeCard(selectID) {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	console.log(selectID);

	var data2 = {};
	data2["cardvalue"] = selectID;
	data2["sessionID"] = sessionID;

	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/changeCard?",
		data: JSON.stringify(data2),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			fire_ajax_submitContract();
		},
		error: function(e) {
			var json = "<h4>Ajax Error Change Card</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

function unhidePlus(ele) {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	var t = "+";
	var b = 1;
	if (ele.innerHTML === "+") {
		t = "-";
		b = 0;
	}
	elem = ele.nextSibling;
	while (elem) {
		if (b)
			elem.setAttribute("hidden", "");
		else
			elem.removeAttribute("hidden");
		elem = elem.nextSibling;
	};
	ele.innerHTML = t;
}

function sendValue(ele) {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	//console.log(ele.name);
	//console.log(ele.value);

	var data2 = {};
	data2["variable"] = ele.name;
	data2["value"] = ele.value;
	data2["sessionID"] = sessionID;

	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/setValue",
		data: JSON.stringify(data2),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			console.log("fine");
			fire_ajax_submitContract();
		},
		error: function(e) {
			var json = "<h4>Ajax Error Send Value</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

function analyzeContract() {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	//console.log(ele.name);
	//console.log(ele.value);

	var data2 = {};
	data2["sessionID"] = sessionID;

	//delete old results
	var eleR = document.getElementById("result");
	removeAllChildNodes(eleR);
	eleR = document.getElementById("feedback");
	removeAllChildNodes(eleR);

	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/analyzeContract",
		data: JSON.stringify(data2),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			fire_ajax_submitContract();
		},
		error: function(e) {
			var json = "<h4>Ajax Error Analyze</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

function analyzeActions() {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	//console.log(ele.name);
	//console.log(ele.value);

	var data2 = {};
	data2["sessionID"] = sessionID;

	//delete old results
	var eleR = document.getElementById("result");
	removeAllChildNodes(eleR);
	eleR = document.getElementById("feedback");
	removeAllChildNodes(eleR);

	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/analyzeActions",
		data: JSON.stringify(data2),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			fire_ajax_submitContract();
		},
		error: function(e) {
			var json = "<h4>Ajax Error Analyze</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

function getActions() {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	//console.log(ele.name);
	//console.log(ele.value);

	var data2 = {};
	data2["sessionID"] = sessionID;

	//delete old results
	var eleR = document.getElementById("diagram");
	removeAllChildNodes(eleR);
	eleR = document.getElementById("actions");
	removeAllChildNodes(eleR);

	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/getActions",
		data: JSON.stringify(data2),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			fire_ajax_submitContract();
		},
		error: function(e) {
			var json = "<h4>Ajax Error Analyze</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

function changeValOn(ele) {
	//	var id = ele.id.replace("_on", "_value");
	//	var idR = ele.id.replace("_on", "");
	//	var node = document.getElementById(id);
	//	var nodeR = document.getElementById(idR);
	//	if (ele.value == 0)
	//		node.value = "";
	//	else
	//		node.value = nodeR.value;
}

function changeRangeVal(ele) {
	var id2 = ele.id + "_value";
	var node2 = document.getElementById(id2);
	node2.value = ele.value;
}

function fire_ajax_logger() {
	var sessionID = $("meta[name='runID']").attr("value");
	var csrfToken = $("meta[name='_csrf']").attr("content");
	var csrfHeader = $("meta[name='_csrf_header']").attr("content");
	$.ajax({
		type: "POST",
		contentType: "application/json",
		url: "/log/msg?",
		data: JSON.stringify(sessionID),
		dataType: 'json',
		cache: false,
		timeout: 600000,
		beforeSend: function(xhr) {
			xhr.setRequestHeader(csrfHeader, csrfToken);
		},
		success: function(data) {
			var msg = data["msg"];
			if (msg) {
				var para = document.createElement("div");
				$(para).html(msg);
				document.getElementById("feedback").appendChild(para);
			}
			var logList = data["logList"];
			if (logList)
				for (var i = 0; i < logList.length; i++) {
					var para = document.createElement("div");
					$(para).html(logList[i]);
					document.getElementById("feedback").appendChild(para);
				}
			var resultList = data["resultList"];
			if (resultList)
				for (var j = 0; j < resultList.length; j++) {
					console.log(resultList[j]);
					var para = document.createElement("div");
					$(para).html(resultList[j]);
					document.getElementById("result").appendChild(para);
					eval($(para).find("script").text());
				}
			//var json = "<pre>"+ JSON.stringify(logList, null, 4) + "</pre>";
		},
		error: function(e) {
			var json = "<h4>Ajax Error Logger</h4><pre>" + e.responseText
				+ "</pre>";
			$('#feedback').html(json);
			console.log("ERROR : ", e);
		}
	});
}

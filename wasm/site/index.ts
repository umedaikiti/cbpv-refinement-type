import "./style.css";

import("../pkg/").then(wasm => {
	wasm.init();
	const examples = require("./examples.json");
	let select = document.getElementById("examples");
	Object.keys(examples).forEach(key => {
		let example = document.createElement("option");
		example.setAttribute("value", key);
		example.innerHTML = key;
		select.appendChild(example);
	});
	select.addEventListener("change", (event) => {
		(<HTMLInputElement>document.getElementById("input")).value = examples[(<HTMLInputElement>event.target).value];
	});
	function create_ast_list(ast) : HTMLElement {
		if(ast.Term) {
			let li = document.createElement("li");
			let name_type = document.createElement("span");
			name_type.appendChild(document.createTextNode(ast.Term.name + " : " + ast.Term.type));
			li.appendChild(name_type);
			let children = document.createElement("ul");
			ast.Term.children.forEach((child) => {
				children.appendChild(create_ast_list(child));
			});
			if(ast.Term.children.length > 0) {
				children.classList.add("nested", "active");
				name_type.classList.add("caret", "caret-down");
				name_type.addEventListener("click", function() {
					this.parentElement.querySelector(".nested").classList.toggle("active");
					this.classList.toggle("caret-down");
				});
			}
			li.appendChild(children);
			return li;
		} else if(ast.Binder) {
			let li = document.createElement("li");
			let name_type = document.createElement("span");
			name_type.appendChild(document.createTextNode("[" + ast.Binder.name + " : " + ast.Binder.type + "]"));
			li.appendChild(name_type);
			let children = document.createElement("ul");
			children.appendChild(create_ast_list(ast.Binder.child));
			li.appendChild(children);
			return li;
		}
		console.log("error");
	}
	function show_result(result) {
		let output = <HTMLInputElement>document.getElementById("output");
		if (result.smtlib === undefined || result.smtlib === null) {
			output.value = "";
			document.getElementById("download").removeAttribute("href");
		} else {
			output.value = result.smtlib;
			let blob = new Blob([ result.smtlib ], { "type" : "text/plain" });;
			(<HTMLAnchorElement>document.getElementById("download")).href = window.URL.createObjectURL(blob);
		}
		let ast_div = document.getElementById("ast");
		while(ast_div.firstChild) {
			ast_div.removeChild(ast_div.firstChild);
		}
		if (result.ast !== undefined && result.ast !== null) {
			let ast_list = document.createElement("ul");
			ast_list.setAttribute("style", "margin: 0; padding: 0;");
			ast_list.appendChild(create_ast_list(result.ast));
			ast_div.appendChild(ast_list);
		}
	}
	document.getElementById("cbv-button").addEventListener("click", function() {
		let input = <HTMLInputElement>document.getElementById("input");
		let simplify = (<HTMLInputElement>document.getElementById("simplify")).checked;
		let result = wasm.to_smtlib_cbv(input.value, simplify);
		show_result(result);
	});
	document.getElementById("cbn-button").addEventListener("click", function() {
		let input = <HTMLInputElement>document.getElementById("input");
		let simplify = (<HTMLInputElement>document.getElementById("simplify")).checked;
		let result = wasm.to_smtlib_cbn(input.value, simplify);
		show_result(result);
	});
});

'use strict';

import "./style.css";

interface Term {
	name: string;
	type: string;
	children: AST[];
}
interface Binder {
	name: string;
	type: string;
	child: AST;
}
type AST = { Term: Term; } | { Binder: Binder; };
interface Result {
	smtlib?: string | null;
	ast?: AST | null;
}

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
		let key = (event.target as HTMLInputElement).value as keyof (typeof examples);
		(document.getElementById("input") as HTMLInputElement).value = examples[key];
	});
	function create_ast_list(ast : AST) : HTMLElement {
		if("Term" in ast) {
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
		} else if("Binder" in ast) {
			let li = document.createElement("li");
			let name_type = document.createElement("span");
			name_type.appendChild(document.createTextNode("[" + ast.Binder.name + " : " + ast.Binder.type + "]"));
			li.appendChild(name_type);
			let children = document.createElement("ul");
			children.appendChild(create_ast_list(ast.Binder.child));
			li.appendChild(children);
			return li;
		}
		const _exhaustiveCheck: never = ast;
		console.log("error");
	}
	function show_result(result : Result) : void {
		let output = document.getElementById("output") as HTMLInputElement;
		if (result.smtlib === undefined || result.smtlib === null) {
			output.value = "";
			document.getElementById("download").removeAttribute("href");
		} else {
			output.value = result.smtlib;
			let blob = new Blob([ result.smtlib ], { "type" : "text/plain" });;
			(document.getElementById("download") as HTMLAnchorElement).href = window.URL.createObjectURL(blob);
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
		let input = document.getElementById("input") as HTMLInputElement;
		let simplify = document.getElementById("simplify") as HTMLInputElement;
		let result = wasm.to_smtlib_cbv(input.value, simplify.checked);
		show_result(result);
	});
	document.getElementById("cbn-button").addEventListener("click", function() {
		let input = document.getElementById("input") as HTMLInputElement;
		let simplify = document.getElementById("simplify") as HTMLInputElement;
		let result = wasm.to_smtlib_cbn(input.value, simplify.checked);
		show_result(result);
	});
});

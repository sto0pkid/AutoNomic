var cases = {
  "GND":{},
  "p":[
	{
	 head:{pred: "p", args:[{pred: ":A", args:[]}, {pred: ":B", args:[]}]}, 
	 body: []
	},

	{
	 head: { pred:"p", args:[{pred:"?y", args:[]}, {pred:"?x", args:[]}]}, 
	 body:[
	 {pred:"p", args:[{pred:"?x", args:[]}, {pred:"?y", args:[]}]}]
	} 
],
  "":[
    {head:{}, body:[{pred:"p", args:[{pred:"?what", args:[]}, {pred:":A", args:[]}]}]}
  ]
}


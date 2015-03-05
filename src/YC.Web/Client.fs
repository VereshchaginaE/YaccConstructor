namespace YC.Web

open WebSharper
open WebSharper.JavaScript
open WebSharper.Html.Client
open WebSharper.JQuery
open WebSharper.JQueryUI

[<JavaScript>]
module Client =
        
    let SetAttr attr value elem =
        elem
        |>! OnAfterRender (fun elem ->
            JQuery.JQuery.Of(elem.Body).Attr(attr, value).Ignore)

    let vSpace (h:int) =
        Div []
        |> SetAttr "height" (string h + "px")

    let hBox (elems: List<Pagelet>) = 
        Div(elems |> List.map (fun e -> Div [e] |> SetAttr "class" "hb-block"))
        -< [Div[] |> SetAttr "class" "clearer"]
        |> SetAttr "class" "hb-row"

    let vBox (elems: List<Pagelet>) = 
        Div(elems |> List.map (fun e -> Div [e] |> SetAttr "class" "vb-block" ))
        -< [Div[] |> SetAttr "class" "clearer"]

    let Start input k =
        async {
            let! data = Remoting.Process(input)
            return k data
        }
        |> Async.Start

    let algoPage algoName =        
        let algoDescription = Div [Text "description"]
        let l1 = Div [TextArea []]
        let l2 = Div [TextArea []]
        let runBtn = Button.New "Run"
        let codeTabs = 
            Tabs.New([("dd",l1); ("eee",l2)], new TabsConfiguration())
            |> SetAttr "id" "tabs-nohdr"
        let pictures = Div[Text "Picts"]
        let page = Div [vBox[Text algoName; hBox [vBox[codeTabs; vSpace 10; runBtn]; pictures]; algoDescription]]
        algoName, page
    
    let Main () =
        let p1 = algoPage "Algo1"
        let p2 = algoPage "Algo2"
        let p3 = algoPage "Algo3"
        let conf = new TabsConfiguration()        
        let codeTabs =        
            Tabs.New([p1; p2; p3]) |> SetAttr "id" "tabs-left"

        Div [codeTabs]
        |> SetAttr "height" "100%"
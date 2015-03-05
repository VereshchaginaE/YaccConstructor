namespace YC.Web

open WebSharper.Html.Server
open WebSharper
open WebSharper.Sitelets

type Action =
    | Home
    | About

module Controls =

    [<Sealed>]
    type EntryPoint() =
        inherit Web.Control()

        [<JavaScript>]
        override __.Body =
            Client.Main() :> _

module Skin =
    open System.Web

    type Page =
        {
            Title : string
            Body : list<Element>
        }

    let MainTemplate =
        Content.Template<Page>("~/Main.html")
            .With("title", fun x -> x.Title)
            .With("body", fun x -> x.Body)

    let WithTemplate title body : Content<Action> =
        Content.WithTemplate MainTemplate <| fun context ->
            {
                Title = title
                Body = body context
            }

module Site =

    let ( => ) text url =
        A [HRef url] -< [Text text]

    let Links (ctx: Context<Action>) =
        UL [
            LI ["Home" => ctx.Link Home]
            LI ["About" => ctx.Link About]
        ]

    let HomePage =
        Skin.WithTemplate "HomePage" <| fun ctx ->
            [
                Div [Text "Algorithms"]
                Div [new Controls.EntryPoint()]
                //Links ctx
            ]

    let AboutPage =
        Skin.WithTemplate "AboutPage" <| fun ctx ->
            [
                Div [Text "ABOUT"]
                Links ctx
            ]

    let Main =
        Sitelet.Sum [
            Sitelet.Content "/" Home HomePage
            //Sitelet.Content "/About" About AboutPage
        ]

[<Sealed>]
type Website() =
    interface IWebsite<Action> with
        member this.Sitelet = Site.Main
        member this.Actions = [Home; About]

type Global() =
    inherit System.Web.HttpApplication()

    member g.Application_Start(sender: obj, args: System.EventArgs) =
        ()

module Resources =

    open WebSharper.Core.Resources

    type R1() =
        inherit BaseResource ("Tabs.css")
        
    

[<assembly:Require(typeof<Resources.R1>)>]
[<assembly: Website(typeof<Website>)>]
do ()
